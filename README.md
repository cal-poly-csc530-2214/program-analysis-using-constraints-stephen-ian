## Analyzing programs through constraint solving

# Overview of our work done
We built a "front-end" for converting Python code to cut-sets based on flow of CFG blocks.

Our program identifies back flows in the CFG to create cut sets based on loops in the source code.

Then, it gathers information on state (i.e. assignments) before, during, and after the loop to generate 2nd-order constraints.

We ran out of time to implement further integration with Z3, which would be possible after converting our 2nd-order constraints to first order.