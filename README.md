# Anomaly cancellation in Lean 4 
Copyright: Joseph Tooby-Smith 

As a proof-of-concept of the use of lean 4 in high energy physics, we create a lean-4 project of results related to annomaly cancellation in physics. My aim is to slowly expand it other areas of high energy physics creating a project called `HEPLean`. 

To learn more about this project see: 

https://leanprover.zulipchat.com/#narrow/stream/395462-Natural-sciences/topic/Anomaly.20cancellation.20conditions



## Installation

### Installing Lean 4 

See: https://leanprover-community.github.io/get_started.html

### Quick installation 

1. Clone this repository. 
2. Open a terminal in the cloned directory. 
2. Run `lake -Kenv=dev update`.

Depending on how up to date this directory is compared to MathLib4 this may lead to errors.

## Docs 

The documentation for this project can be generated using 

https://github.com/leanprover/doc-gen4

1. Open a terminal in the `AnomalyCancellationInLean` directory.
2. Run `lake -R -Kenv=dev build AnomalyCancellationInLean:docs` to generat the docs. Since this generates all the docs for Mathlib4 as well - this takes a long time to run.

To view the docs: 

3. Open the directory `.lake/build/doc` by running `cd .lake/build/doc`. 
4. Run `python3 -m http.server`
5. Open `.lake/build/doc/index.html` 

## Workflows 

This github repository uses a number of workflows.

- `lean-upgrade-action` found at https://github.com/leanprover-contrib/lean-upgrade-action

Run lint using (TODO : Make into workflow): 

`./.lake/packages/mathlib/scripts/lint-style.py $(find AnomalyCancellationInLean -name '*.lean')`