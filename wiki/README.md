<!-- SPDX-FileCopyrightText: © 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk> -->
<!-- SPDX-License-Identifier: CC-BY-SA-4.0 -->
# Wiki source (mirrored in-repo)

These `.md` pages are the source for the project's GitHub wiki, kept in-repo so they
are versioned, reviewed, and never lost.

**Note:** The GitHub wiki is **enabled** (`has_wiki: true`) but was **never initialised**, so the
`*.wiki.git` remote does not yet exist and cannot be pushed to. This is a one-time
manual bootstrap:

1. In the GitHub UI, open **Wiki** and **Create the first page** (any content — it can be
   empty; it just initialises the wiki git repo).
2. Then publish these pages:

```sh
git clone git@github.com:hyperpolymath/trope-checker.wiki.git /tmp/tc-wiki
cp wiki/Home.md wiki/Tropical-Factorisation-Probe.md /tmp/tc-wiki/
( cd /tmp/tc-wiki && git add -A && git commit -m "wiki: Home + Tropical Factorisation Probe" && git push )
```

Page ↔ file mapping (GitHub wiki uses the file basename as the page title):

| Page | Purpose |
| --- | --- |
| `Home.md` | Wiki landing page — verification streams, gates, honesty pointers. |
| `Tropical-Factorisation-Probe.md` | The probe write-up — verdict (B), proved theorems, the necessary-not-sufficient guard. |
