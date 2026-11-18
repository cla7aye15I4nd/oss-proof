"""Build the zlib subsite under site/dist/zlib/."""
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))

from pagekit import GIT_ROOT, OUT, SUITE_OUT
from reference import build_reference
from reading import build_reading
from home import build_home


def build_zlib_site() -> None:
    SUITE_OUT.mkdir(parents=True, exist_ok=True)
    if OUT.exists():
        shutil.rmtree(OUT)
    OUT.mkdir(parents=True)
    shutil.copytree(ROOT / 'static', OUT / 'static')
    shutil.copyfile(ROOT / 'content/codec-trace.json', OUT / 'static/examples/codec-trace.json')
    shutil.copyfile(ROOT / 'content/codec-playground-provenance.json', OUT / 'static/examples/codec-playground-provenance.json')
    build_reference()
    build_reading()
    build_home()


if __name__ == '__main__':
    build_zlib_site()
    if not (SUITE_OUT / 'en/index.html').exists():
        sys.path.insert(0, str(GIT_ROOT / 'site'))
        import portal
        portal.build_portal()
