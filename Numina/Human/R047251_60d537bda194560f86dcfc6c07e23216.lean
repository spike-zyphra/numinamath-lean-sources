import Mathlib

/- Feri wrote on the board

$$
\frac{19^{3}+65^{3}}{46^{3}+65^{3}}
$$

and "simplified" the expression by erasing the exponents, stating that the resulting expression is equal to the original one. Gábor warned him to be careful, but Feri demonstrated the equality of the two expressions with calculations and showed more similar numerical examples. Gábor is still worried that the procedure is not always valid. Can we support Feri's method? Or should we address Gábor's concerns? -/
theorem algebra_179459 : (19^3 + 65^3) / (46^3 + 65^3) = (19 + 65) / (46 + 65) := by ring