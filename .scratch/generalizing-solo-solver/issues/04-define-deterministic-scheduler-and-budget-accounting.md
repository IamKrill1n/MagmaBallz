# Define deterministic scheduler and budget accounting

Status: open
Type: prototype
Blocked by: 02, 03, 05, 06, 07

## Question

How should the solver allocate reproducible work quotas across cheap stages,
countermodel search, proof search, certificate generation, and potentially slow
judge calls within an adjustable 300-second safety deadline, both with and
without a direction prediction?
