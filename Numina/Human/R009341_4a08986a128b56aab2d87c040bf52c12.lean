import Mathlib
open Mathlib

/--
Last year Mr. Jon Q. Public received an inheritance. He paid $20\%$ in federal taxes on the inheritance, and paid $10\%$ of what he had left in state taxes. He paid a total of $\textdollar10500$ for both taxes. How many dollars was his inheritance?
$(\mathrm {A})\ 30000 \qquad (\mathrm {B})\ 32500 \qquad(\mathrm {C})\ 35000 \qquad(\mathrm {D})\ 37500 \qquad(\mathrm {E})\ 40000$
-/
lemma algebra_1181 (inheritance : ℚ) (totalTax : (20 : ℚ) / 100 * inheritance + (inheritance - (20 : ℚ) / 100 * inheritance) * (10 : ℚ) / 100 = 10500) : inheritance = 37500 := by
  -- After paying his taxes, he has $0.8*0.9=0.72$ of his earnings left.
  have djs : (1 - (0.72 : ℚ)) * inheritance = 10500 := by linarith
  -- Since $10500$ is $0.28$ of his income, he got a total of $\frac{10500}{0.28}=37500
  have skd : inheritance = 10500 / 0.28 := by linarith
  rw [skd]
  norm_num