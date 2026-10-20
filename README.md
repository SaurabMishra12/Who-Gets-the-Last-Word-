Who Gets the Last Word?
Companion artifacts for Auditing Communication and Readout in Multi-Agent Web Question Answering
Purpose
This repository asks how a communication graph changes the final answer when evidence, recipient updates, and readout are accounted for separately. It contains the records behind the reported comparisons, along with small offline tools for inspecting them.
Start here
Run the following commands from the repository root:
python evaluation/verify_release.py
python evaluation/recompute.py /tmp/lastword_results.json
python evaluation/verify_formal.py
python figures/render.py /tmp/lastword-figures
Requirements
Task	Requirement
Offline checks	Python 3.10 or later; standard library only
Formal check	Lean 4.16.0 and Lake installed
Figure rendering	Matplotlib 3.8 or later


Repository contents
Path	Description
tables/paper	All eleven paper tables as TeX fragments and CSV cells. Table 3 is transcribed from the supplied PDF; the other fragments come from the earlier supplied TeX and retain reported values.
results	Per-question outcomes, paired contrasts, cohort summaries, and resource reports.
raw_outputs	Saved result records and returned answer content, including unsuccessful answers and refusals.
prompts	Exact archived Web request messages and source-extracted historical prompt templates.
configs	Frozen run settings, model details, and controller parameters.
data	Dataset descriptions, cohort sizes, and evaluation references.
algorithms	Pseudocode describing the execution contract.
formal	Lean sources for the encoded communication and readout models.
figures	CSV observations and a rendering script for companion versions of the four figures.
provenance	Source hashes, release hashes, accounting summaries, and validation records.


Reading the results
- Historical 2Wiki study: The study has a 20-question pilot and a 130-question extension. The incoming star and dense graph reuse the same sink request. Their fixed-sink agreement is therefore a property of the execution contract, not an independent test of model determinism.
- Peer/private study: This study uses 130 previously inspected training questions. The separate development cohort has 60 questions. Peer revision gets 96 and 31 answers correct, respectively; private revision gets 22 and 8. These are paired comparisons under one deployment and one prompt protocol.
- HotpotQA readout analyses: These analyses reuse saved predictions. Removing abstentions from the vote changes the decision rule without adding inference. Gold coverage is an availability diagnostic, not proof of semantic source necessity.
- P1 and P1b: P1 seed summaries and P1b paired cohorts have different denominators. Historical reasoning archives contain repeated questions and checkpoint slices.
- P4 and P5: These use arithmetic templates. P5 communication totals are word-based proxies, so they should not be read as provider-token measurements on a verified GSM8K sample.
Release scope
This is a partial audit release. It supports answer-score recomputation and inspection of saved outputs. The production runner, training implementation, and controller weights are not included, so the repository does not reproduce the full experiment from fresh model calls. Method details and prompts may still permit an independent reimplementation.
Record handling
Returned answer content is retained. Provider connection details, transport headers, and internal reasoning fields are omitted. JSONL archives are serialized as JSON arrays in source order; duplicate rows are preserved.

Source hashes identify the original records, while release hashes identify the exported files. An original embedded envelope hash is not a checksum of a redacted export.
Prompt coverage
All saved requests in the selected canonical Web run directories are included. Some inherited cache responses do not have a request file in those directories. Historical reasoning streams do not retain every instantiated prompt; source-derived text templates are supplied and are not presented as raw request records.
Costs and usage accounting
Logical calls and tokens describe an execution policy. Physical ledgers describe provider attempts. Shared cached responses make arm totals nonadditive. Missing usage and unresolved attempts remain unknown; token lower bounds are not a measured currency bill.
Version and figure provenance
This release refers to Agentic_AI (5).pdf, identified by SHA-256 in paper/reference.json. The earlier TeX bundle predates the peer/private table. Figure renderings preserve released observations but do not reproduce the original artwork pixel for pixel.
Rights
Benchmark excerpts retain their upstream terms. No blanket license is asserted over third-party data or model outputs. No model or dataset license is changed by this repository.
Verification limits
The offline scripts check released scores and selected readouts. They do not independently verify factual faithfulness, data contamination, source necessity, scientific novelty, or every historical confidence interval. Lean checks the stated encoded assumptions, not the empirical behavior of the model.
