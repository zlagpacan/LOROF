# FPU contribution guidance

## Testbench development

- Follow the existing cycle-by-cycle style in neighboring FPU SystemVerilog testbenches. Keep stimulus and expected outputs explicit in the test sequence so cycle timing and each checked result are easy to review.
- Use the existing `@(posedge CLK); #(PERIOD/10);` timing convention at the same points as nearby tests. Keep checks aligned to the intended cycle and make backpressure or throughput behavior explicit when it is under test.
- Prefer enumerated test cases and the bench's existing output-checking task. Do not introduce a generic `run_case()` task or hide a sequence of cycles behind a case helper when the surrounding benches enumerate them directly.
- Preserve the surrounding bench's indentation, comments, naming, and display format. Do not add extra checker latency to a single-cycle completion path unless the interface behavior requires it.

## Module interfaces

- The user designs module I/O. Treat FPU ports and externally visible interface signals as user-owned: do not add, remove, rename, resize, reorder, or repurpose them without explicit direction.
- If the intended interface or meaning of an I/O signal is unclear, ask for clarification before changing it. Continue with internal implementation work that does not depend on that ambiguity.
