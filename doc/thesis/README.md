# PhD thesis

[`2014-10-28-phd-thesis.pdf`](2014-10-28-phd-thesis.pdf) is Colm Bhandal, *"Formalising a Real-Time Coordination Model"*, PhD thesis, Trinity College Dublin, 28 October 2014. It defines the language, the Comhordú protocol and the safety result that `src/` formalises. It is also on [TARA](http://www.tara.tcd.ie/bitstream/handle/2262/77596/Bhandal%2c%20Colm_TCD-SCSS-PHD-2014-08.pdf?sequence=1&isAllowed=y) as report TCD-SCSS-PHD-2014-08.

The PDF's page numbers run 12 ahead of the printed ones: printed p.122 is PDF page 134. Older documents, such as the [pass-1 report](../reports/2026-10-14-proof-completion-pass-1/README.md), cite PDF pages.

The thesis says that its proof is partly encoded in Coq (Summary, p.ii) and that the proofs of chapter 6 follow the Coq proof (p.140). That is no longer true. The formalisation in `src/` is now in Rocq, and while it proves the same safety result, its proof has been simplified and improved, and departs from the thesis's in many details. Those departures are not recorded.

Errors in the thesis itself are corrected in [`thesis-corrections.md`](thesis-corrections.md). Notable observations about the thesis that are not errors in it are in [`thesis-remarks.md`](thesis-remarks.md).
