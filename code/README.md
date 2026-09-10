# Course code

Lake project holding the Lean the students see: the live-coding lecture files
`Course/LectureNN.lean`, the seminar exercise files `Course/SeminarNN.lean`,
and the support code the homework statements talk about. Lecture and seminar
files are published only up to the repo's `published-through` cap.

## Setup

```
lean-cache use   # links .lake/packages at the shared Mathlib overlay
lake build
```

Toolchain and Mathlib are pinned together at v4.33.0. See the root README's
Lake-projects section for what `lean-cache use` and the committed
`lake-manifest.json` do. Don't run `lake update` — it will try to write into
the overlay.
