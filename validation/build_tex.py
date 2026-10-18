"""Build a manuscript directory with pdflatex/bibtex in a scratch copy; write the PDF to output/pdf/<name>.pdf.

Usage: python validation/build_tex.py <tex-dir> <out-name>
The scratch copy avoids bibtex path problems with an external -outdir and keeps the source tree clean.
"""
import pathlib, shutil, subprocess, sys, tempfile

def main(src: str, name: str) -> int:
    src_dir = pathlib.Path(src).resolve()
    out = pathlib.Path(__file__).resolve().parent.parent / "output" / "pdf"
    out.mkdir(parents=True, exist_ok=True)
    tex = "SelfModifyingCodeTamperProofingManuscriptUpdated"
    with tempfile.TemporaryDirectory() as tmp:
        for f in src_dir.iterdir():
            if f.is_file() and f.suffix in {".tex", ".bib", ".eps", ".bst", ".sty"}:
                shutil.copy(f, tmp)
        def run(*cmd):
            return subprocess.run(list(cmd), cwd=tmp, capture_output=True, text=True, encoding="utf-8", errors="replace")
        # no latexmk needed: pdflatex, bibtex, pdflatex x2
        r = run("pdflatex", "-interaction=nonstopmode", f"{tex}.tex")
        run("bibtex", tex)
        run("pdflatex", "-interaction=nonstopmode", f"{tex}.tex")
        r = run("pdflatex", "-interaction=nonstopmode", f"{tex}.tex")
        pdf = pathlib.Path(tmp) / f"{tex}.pdf"
        log = (pathlib.Path(tmp) / f"{tex}.log").read_text(encoding="utf-8", errors="replace")
        undefined = log.count("undefined")
        if pdf.exists():
            shutil.copy(pdf, out / f"{name}.pdf")
        print(f"{name}: pdflatex exit {r.returncode}, pdf={'yes' if pdf.exists() else 'NO'}, 'undefined' lines={undefined}")
        return 0 if r.returncode == 0 and pdf.exists() else 1

if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
