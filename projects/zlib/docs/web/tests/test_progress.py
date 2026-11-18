"""The status page must say what the records say, in both languages, and nothing internal."""
from pathlib import Path
import re
import sys
import unittest

SITE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SITE))
import progress
from home import RESULTS, result_done, result_goals

DOCS = SITE.parent
PAGES = {'en': (DOCS / 'en/progress.md').read_text(), 'zh': (DOCS / 'zh/progress.md').read_text()}


def result_rows(text):
    """Rows `| n | result | goals | state |` of the results table."""
    rows = {}
    for line in text.splitlines():
        cells = [cell.strip() for cell in line.strip().strip('|').split('|')]
        if line.startswith('|') and len(cells) == 4 and cells[0].isdigit():
            rows[int(cells[0])] = (re.findall(r'`Goal\.(\w+)`', cells[2]), cells[3])
    return rows


class StatusPage(unittest.TestCase):
    def test_every_function_with_a_goal_has_one_row_with_its_state(self):
        expected = {f.name: f for f in progress.functions() if f.goal}
        for lang, text in PAGES.items():
            rows = [row for row in progress.page_rows(text) if row[0] in expected]
            self.assertEqual(sorted(row[0] for row in rows), sorted(expected), lang)
            for name, goal, shown in rows:
                self.assertEqual(goal, expected[name].goal, (lang, name))
                self.assertEqual(shown, progress.state(expected[name].done, lang), (lang, name))

    def test_the_other_goals_are_listed_once_with_their_state(self):
        owned = {f.name for f in progress.functions()}
        for lang, text in PAGES.items():
            rows = [row for row in progress.page_rows(text) if row[0] not in owned]
            self.assertEqual(sorted(row[1] for row in rows),
                             sorted(progress.other_goals() + progress.roundtrip_goals()), lang)
            for _, goal, shown in rows:
                self.assertEqual(shown, progress.state(progress.goal_done(goal), lang), (lang, goal))

    def test_the_rows_are_exactly_the_goals_of_the_four_results(self):
        safety, roundtrip = progress.required_goals(), progress.roundtrip_goals()
        self.assertFalse(set(safety) & set(roundtrip))
        for lang, text in PAGES.items():
            listed = [row[1] for row in progress.page_rows(text)]
            self.assertEqual(sorted(listed), sorted(safety + roundtrip), lang)
            for number in (len(safety), len(roundtrip)):
                self.assertIn(str(number), text.split('##')[0], (lang, 'the stated number of goals'))

    def test_the_results_agree_with_the_home_page_and_the_records(self):
        for lang, text in PAGES.items():
            rows = result_rows(text)
            self.assertEqual(sorted(rows), [number for number, *_ in RESULTS], lang)
            for number, decided, *_ in RESULTS:
                goals, shown = rows[number]
                if decided:
                    self.assertEqual(tuple(goals), decided, (lang, number))
                else:
                    self.assertEqual(goals, [], (lang, number))
                self.assertEqual(shown, progress.state(result_done(decided), lang), (lang, number))
        taken = [goal for _, decided, *_ in RESULTS for goal in result_goals(decided)]
        self.assertEqual(sorted(taken), sorted(progress.required_goals() + progress.roundtrip_goals()))

    def test_functions_without_a_safety_goal_are_named_as_not_planned(self):
        missing = [f.name for f in progress.functions() if not f.goal]
        self.assertTrue(missing)
        for lang, text in PAGES.items():
            section = text.split('{#not-planned}', 1)[1]
            for name in missing:
                self.assertIn('`' + name + '`', section, (lang, name))

    def test_only_two_states_and_no_internal_vocabulary(self):
        states = {'en': {'done', 'not done'}, 'zh': {'完成', '未完成'}}
        banned = [r'\bchecked\b(?! the proof)', r'\bregistered\b', r'\baccepted\b', r'\bfast gate\b', r'\bcommit\b',
                  r'tests/audit', r'\bmilestone\b', r'\bmutant', r'已检查', r'已登记', r'已验收', r'快速关卡', r'提交']
        for lang, text in PAGES.items():
            for _, _, shown in progress.page_rows(text):
                self.assertIn(shown, states[lang])
            for _, shown in result_rows(text).values():
                self.assertIn(shown, states[lang])
            for pattern in banned:
                self.assertIsNone(re.search(pattern, text, re.I), (lang, pattern))

    def test_both_languages_have_the_same_rows(self):
        en = [(name if name.isascii() and ' ' not in name else '', goal) for name, goal, _ in progress.page_rows(PAGES['en'])]
        zh = [(name if name.isascii() and ' ' not in name else '', goal) for name, goal, _ in progress.page_rows(PAGES['zh'])]
        self.assertEqual(en, zh)


LISTS = '''
def proved : List (Name × Name) := [
  -- a group
  (``A.Goal.one, ``A.one),
  (``A.Goal.two, ``A.two)
]

/-- Not done. -/
def notDone : List Name := [
  ``A.Goal.three
]

def required : List Name := [
  ``A.Goal.one
]
'''


class ResultsReader(unittest.TestCase):
    """The reader of ZlibF/Results.lean works on the text alone and refuses what it cannot read."""

    def test_the_three_lists_are_read(self):
        lists = progress.parse_results(LISTS)
        self.assertEqual(lists.proved, (('A.Goal.one', 'A.one'), ('A.Goal.two', 'A.two')))
        self.assertEqual(lists.not_done, ('A.Goal.three',))
        self.assertEqual(lists.required, ('A.Goal.one',))

    def test_comments_are_removed_and_strings_are_kept(self):
        text = 'a -- line /- not open\nb /- one /- nested -/ still -/ c /-- doc -/ d "-- /- kept" e'
        stripped = progress.strip_comments(text)
        self.assertEqual(stripped.split(), ['a', 'b', 'c', 'd', '"--', '/-', 'kept"', 'e'])
        self.assertEqual(len(stripped), len(text))
        self.assertEqual(stripped.count('\n'), text.count('\n'))

    def test_an_entry_inside_a_comment_is_not_an_entry(self):
        for hidden in ('  -- (``A.Goal.two, ``A.two)', '  /- (``A.Goal.two, ``A.two) -/',
                       '  /- /- nested -/ (``A.Goal.two, ``A.two) -/'):
            text = LISTS.replace('  (``A.Goal.one, ``A.one),\n  (``A.Goal.two, ``A.two)',
                                 '  (``A.Goal.one, ``A.one)\n' + hidden)
            self.assertEqual(progress.parse_results(text).proved, (('A.Goal.one', 'A.one'),), hidden)

    def test_a_list_inside_a_comment_is_not_the_list(self):
        fake = '/-\ndef proved : List (Name × Name) := [\n  (``A.Goal.three, ``A.three)\n]\n-/\n'
        self.assertEqual(progress.parse_results(fake + LISTS), progress.parse_results(LISTS))

    def test_a_required_goal_that_is_not_proved_is_refused(self):
        with self.assertRaisesRegex(progress.ResultsError, 'required goal is not in `proved`: A.Goal.three'):
            progress.parse_results(LISTS.replace('  ``A.Goal.one\n]', '  ``A.Goal.one,\n  ``A.Goal.three\n]'))
        with self.assertRaisesRegex(progress.ResultsError, 'required goal is not in `proved`: A.Goal.two'):
            progress.parse_results(LISTS.replace('  (``A.Goal.two, ``A.two)', '  /- (``A.Goal.two, ``A.two) -/')
                                   .replace('``A.one),', '``A.one)')
                                   .replace('  ``A.Goal.one\n]', '  ``A.Goal.one,\n  ``A.Goal.two\n]'))

    def test_an_empty_or_missing_list_is_refused(self):
        with self.assertRaisesRegex(progress.ResultsError, '`required` is empty'):
            progress.parse_results(LISTS.replace('  ``A.Goal.one\n]', '  -- ``A.Goal.one\n]'))
        with self.assertRaisesRegex(progress.ResultsError, '`notDone` is empty'):
            progress.parse_results(LISTS.replace('  ``A.Goal.three\n', ''))
        with self.assertRaisesRegex(progress.ResultsError, '`proved` is defined 0 times'):
            progress.parse_results(LISTS.replace('def proved', 'def other'))
        with self.assertRaisesRegex(progress.ResultsError, '`required` is defined 2 times'):
            progress.parse_results(LISTS + 'def required : List Name := [\n  ``A.Goal.two\n]\n')

    def test_text_that_is_not_an_entry_is_refused(self):
        with self.assertRaisesRegex(progress.ResultsError, 'not an entry'):
            progress.parse_results(LISTS.replace('``A.Goal.three', '``A.Goal.three ++ more'))
        with self.assertRaisesRegex(progress.ResultsError, 'not an entry'):
            progress.parse_results(LISTS.replace('(``A.Goal.two, ``A.two)', '(``A.Goal.two)'))
        with self.assertRaisesRegex(progress.ResultsError, 'not closed'):
            progress.parse_results(LISTS + '/- open')

    def test_a_goal_listed_twice_is_refused(self):
        with self.assertRaisesRegex(progress.ResultsError, 'listed twice'):
            progress.parse_results(LISTS.replace('``A.Goal.three', '``A.Goal.two'))

    def test_the_module_of_the_repository_is_read_and_agrees_with_the_status_page(self):
        lists = progress.results()
        self.assertTrue(set(lists.required) <= {goal for goal, _ in lists.proved})
        self.assertEqual(len(lists.required), len(progress.required_goals()) + len(progress.roundtrip_goals()))
        self.assertEqual({progress.short(goal) for goal in lists.required},
                         set(progress.required_goals()) | set(progress.roundtrip_goals()))
        for text in PAGES.values():
            self.assertEqual({goal for _, goal, _ in progress.page_rows(text)},
                             {progress.short(goal) for goal in lists.required})


class Records(unittest.TestCase):
    def test_a_goal_without_a_theorem_is_not_done(self):
        self.assertFalse(progress.goal_done(None))
        self.assertFalse(progress.goal_done('ZlibF.Spec.Public.Goal.no_such_goal'))
        self.assertTrue(progress.goal_done('inflate_safety'))

    def test_a_result_without_a_stated_goal_is_not_done(self):
        self.assertFalse(result_done(()))

    def test_a_functional_contract_that_is_not_done_is_not_planned(self):
        self.assertEqual(progress.functional_state(True, 'en'), 'done')
        self.assertEqual(progress.functional_state(True, 'zh'), '完成')
        self.assertEqual(progress.functional_state(False, 'en'), 'not done, not planned')
        self.assertEqual(progress.functional_state(False, 'zh'), '未完成，不在计划内')


if __name__ == '__main__':
    unittest.main()
