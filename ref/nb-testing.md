Great, let me walk you through the main tools and approaches for each testing need.

## Execution/Smoke Testing

**nbmake** — A pytest plugin that runs notebooks and fails if any cell throws an exception.

```bash
pip install nbmake
pytest --nbmake notebooks/
```

Works well in CI/CD pipelines. You can set timeouts and parallelize with `pytest-xdist`.

**nbconvert** — Built-in option using the `--execute` flag:

```bash
jupyter nbconvert --to notebook --execute mynotebook.ipynb
```

Returns non-zero exit code on failure, so it's CI-friendly.

---

## Output/Regression Testing

**nbval** — Pytest plugin that re-executes notebooks and compares outputs against saved outputs:

```bash
pip install nbval
pytest --nbval notebooks/
```

Use `--nbval-lax` to only check for errors without strict output matching. You can mark cells with `# NBVAL_IGNORE_OUTPUT` for non-deterministic outputs.

**testbook** — Lets you write pytest-style unit tests that inject into notebooks and assert on specific cells:

```python
from testbook import testbook

@testbook("notebooks/analysis.ipynb", execute=True)
def test_data_load(tb):
    df = tb.ref("df")  # reference a variable from the notebook
    assert len(df) > 0
```

This is powerful for testing specific logic while keeping the notebook as-is.

---

## Code Quality/Linting

**nbqa** — Runs standard Python linters on notebooks:

```bash
pip install nbqa
nbqa flake8 notebooks/
nbqa black notebooks/  # can also format in-place
nbqa mypy notebooks/
```

---

## CI/CD Integration

A typical GitHub Actions workflow might look like:

```yaml
- name: Test notebooks
  run: |
    pip install nbmake nbqa flake8
    nbqa flake8 notebooks/
    pytest --nbmake --nbmake-timeout=300 notebooks/
```

---

## Restructuring Approach (Secondary)

For critical logic, consider extracting functions into `.py` modules and importing them into notebooks. This lets you write conventional unit tests while keeping notebooks thin. Tools like **jupytext** can help by keeping `.py` and `.ipynb` files in sync.

---

Would you like me to expand on any of these—say, more detail on `testbook` patterns or handling notebooks with side effects (databases, APIs)?