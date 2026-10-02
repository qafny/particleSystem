# Original-branch plots, regenerated 1 October 2026

These replace the earlier redesigned drafts. Plot functions were restored from
`jbg/202603:scripts/plot_results.py`, with current CSV mapping and corrected labels.
All figures use ε=0.1 and t=0.7854, hence a single tolerance panel.

35 matched compiler inputs; 38 matched QBlue inputs for each flower comparison.
OpenFermion has four term-limit errors and one missing path-2 result. QBlue has
296 successful rows and 24 errors. Source CSVs and experiment metrics are unchanged.
The compilers use different error estimates; these figures do not demonstrate equal achieved error.

## Optimization comparison

Original mirrored, smoothed curves: QBlue above the centerline, OpenFermion below. Distances from zero are positive gate counts.

[PNG](t0.7854/tab2_gate_reduction_openfermion.png) · [PDF](t0.7854/tab2_gate_reduction_openfermion.pdf)

## QDrift versus first-order Trotter

Original three-petal flower: one median per size bucket; dashed Trotter and solid QDrift, using pre-optimization counts.

[PNG](t0.7854/fig_qdrift_vs_std_polar.png) · [PDF](t0.7854/fig_qdrift_vs_std_polar.pdf)

## Analog versus digital: single-qubit

Original median flower, using raw full-circuit pre-optimization counts.

[PNG](t0.7854/tab_analog_vs_digital_1q_polar.png) · [PDF](t0.7854/tab_analog_vs_digital_1q_polar.pdf)

## Analog versus digital: multi-qubit

Original median flower; digital gates and analog pulses are counted without a duration adjustment.

[PNG](t0.7854/tab_analog_vs_digital_mq_polar.png) · [PDF](t0.7854/tab_analog_vs_digital_mq_polar.pdf)

## Gates versus Hamiltonian size

Original scatter layout with separate compiler colors.

[PNG](t0.7854/tab2_gate_count_err0.1.png) · [PDF](t0.7854/tab2_gate_count_err0.1.pdf)

## Compiler parity

Each point is one matched input; OpenFermion on x, QBlue on y. Colors indicate size buckets.

[PNG](t0.7854/fig2_scatter_qblue_vs_openfermion_err0.1.png) · [PDF](t0.7854/fig2_scatter_qblue_vs_openfermion_err0.1.pdf)

## Reported compilation time

Original layout using existing compilation_time, with different timing scopes across compilers.

[PNG](t0.7854/tab2_compile_time_err0.1.png) · [PDF](t0.7854/tab2_compile_time_err0.1.pdf)

