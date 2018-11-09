# To do

- Implement a post-processing function that translates back the internal syntax
  of the reduced goal to the surface syntax, prettifying-it in the process (e.g.
  translate ~ (x < y) to (y <= x), etc. *)
- Check that we do not pollute the user with unneeded stuff (notations, tactics,
  Arguments...)
- Extend zify to handle ( | ), ( / ) and ( mod )
- Prove that the term normalization function produces well-formed terms, instead
  of validating it
