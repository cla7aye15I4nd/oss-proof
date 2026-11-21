/* Interactive layer for the call-chain explorer: tabs, chain selection, library focus, hash links.
   Everything it shows is already in the server-rendered HTML; without JS the page lists every chain. */
(function () {
  'use strict';
  const root = document.querySelector('[data-audit-explorer]');
  if (!root) return;
  const zh = document.documentElement.lang === 'zh';
  const t = (cn, en) => (zh ? cn : en);
  const groups = [...root.querySelectorAll('.ax-group')];
  if (!groups.length) return;
  root.classList.add('ax-js');

  const tabs = document.createElement('div');
  tabs.className = 'ax-tabs';
  tabs.setAttribute('role', 'tablist');
  root.insertBefore(tabs, groups[0]);

  const state = new Map();

  groups.forEach((group) => {
    const title = group.querySelector('h3').textContent;
    const tab = document.createElement('button');
    tab.type = 'button';
    tab.className = 'ax-tab';
    tab.setAttribute('role', 'tab');
    tab.textContent = title;
    tab.addEventListener('click', () => showGroup(group.dataset.group, true));
    tabs.appendChild(tab);

    const chains = [...group.querySelectorAll('.ax-chain')];
    const list = group.querySelector('.ax-chains');
    const matrix = group.querySelector('.ax-matrix-wrap');
    const layout = document.createElement('div');
    layout.className = 'ax-layout';
    const nav = document.createElement('nav');
    nav.className = 'ax-nav';
    nav.setAttribute('aria-label', t('调用链', 'Call chains'));
    chains.forEach((chain) => {
      const button = document.createElement('button');
      button.type = 'button';
      button.dataset.chain = chain.dataset.chain;
      const name = chain.querySelector('h4').textContent;
      const libs = chain.dataset.libs.split(' ').filter(Boolean);
      button.innerHTML = '';
      button.append(name);
      const small = document.createElement('small');
      small.textContent = libs.map(libLabel(group)).join(' · ');
      button.appendChild(small);
      button.addEventListener('click', () => showChain(group.dataset.group, chain.dataset.chain, true));
      nav.appendChild(button);
    });
    group.insertBefore(layout, list);
    layout.append(nav, list);
    if (matrix) {
      group.appendChild(matrix);
      const hint = document.createElement('p');
      hint.className = 'ax-hint';
      hint.textContent = t('点击一行切换调用链；点击库名，在所有调用链中标出它。', 'Click a row to switch chains; click a library to mark it in every chain.');
      matrix.appendChild(hint);
      matrix.querySelectorAll('tbody tr').forEach((row) => {
        row.addEventListener('click', (event) => {
          event.preventDefault();
          showChain(group.dataset.group, row.dataset.chain, true);
        });
      });
      matrix.querySelectorAll('thead th[data-lib]').forEach((th) => {
        th.addEventListener('click', () => focusLib(group, th.dataset.lib));
      });
    }
    group.querySelectorAll('.ax-step[data-lib]').forEach((step) => {
      const box = step.querySelector(':scope > .ax-box');
      box.addEventListener('mouseenter', () => hoverLib(group, step.dataset.lib, true));
      box.addEventListener('mouseleave', () => hoverLib(group, step.dataset.lib, false));
    });
    state.set(group.dataset.group, { group, tab, chains, nav, focus: null, current: chains[0] && chains[0].dataset.chain });
  });

  function libLabel(group) {
    return (lib) => {
      const th = group.querySelector('.ax-matrix thead th[data-lib="' + lib + '"]');
      return th ? th.textContent : lib;
    };
  }

  function showGroup(id, push) {
    state.forEach((s, key) => {
      const on = key === id;
      s.group.hidden = !on;
      s.tab.setAttribute('aria-selected', String(on));
    });
    const s = state.get(id);
    showChain(id, s.current, push);
  }

  function showChain(groupId, chainId, push) {
    const s = state.get(groupId);
    if (!s) return;
    state.forEach((other, key) => {
      other.group.hidden = key !== groupId;
      other.tab.setAttribute('aria-selected', String(key === groupId));
    });
    s.current = chainId;
    s.chains.forEach((chain) => {
      const on = chain.dataset.chain === chainId;
      chain.hidden = !on;
      chain.classList.remove('ax-enter');
      if (on) {
        void chain.offsetWidth;
        chain.classList.add('ax-enter');
      }
    });
    s.nav.querySelectorAll('button').forEach((b) => b.setAttribute('aria-current', String(b.dataset.chain === chainId)));
    s.group.querySelectorAll('.ax-matrix tbody tr').forEach((row) => row.classList.toggle('ax-current', row.dataset.chain === chainId));
    if (push) history.replaceState(null, '', '#chain-' + chainId);
  }

  function focusLib(group, lib) {
    const s = state.get(group.dataset.group);
    s.focus = s.focus === lib ? null : lib;
    group.querySelectorAll('.ax-step').forEach((step) => step.classList.toggle('ax-focus', !!s.focus && step.dataset.lib === s.focus));
    group.querySelectorAll('.ax-matrix [data-lib]').forEach((cell) => cell.classList.toggle('ax-focus-col', !!s.focus && cell.dataset.lib === s.focus));
    s.nav.querySelectorAll('button').forEach((b) => {
      const chain = s.chains.find((c) => c.dataset.chain === b.dataset.chain);
      const reaches = chain.dataset.libs.split(' ').includes(s.focus);
      b.classList.toggle('ax-dim', !!s.focus && !reaches);
    });
    if (s.focus) {
      const current = s.chains.find((c) => c.dataset.chain === s.current);
      if (!current.dataset.libs.split(' ').includes(s.focus)) {
        const first = s.chains.find((c) => c.dataset.libs.split(' ').includes(s.focus));
        if (first) showChain(group.dataset.group, first.dataset.chain, true);
      }
    }
  }

  function hoverLib(group, lib, on) {
    group.querySelectorAll('.ax-matrix [data-lib="' + lib + '"]').forEach((cell) => cell.classList.toggle('ax-focus-col', on || state.get(group.dataset.group).focus === lib));
  }

  function fromHash() {
    const m = /^#chain-(.+)$/.exec(location.hash);
    if (m) {
      for (const [id, s] of state) {
        if (s.chains.some((c) => c.dataset.chain === m[1])) {
          showChain(id, m[1], false);
          root.scrollIntoView({ block: 'start' });
          return true;
        }
      }
    }
    return false;
  }

  if (!fromHash()) showGroup(groups[0].dataset.group, false);
  window.addEventListener('hashchange', fromHash);
})();
