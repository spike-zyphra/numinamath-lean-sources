import Mathlib 
/- Sreshtha needs to estimate the quantity $\frac{a}{b} - c$, where $a, b,$ and $c$ are large positive integers. She rounds each of the integers so that the calculation will be easier to do mentally. In which of these situations will her answer necessarily be greater than the exact value of $\frac{a}{b} - c$?
$\textbf{(A)}\ \text{She rounds all three numbers up.}\\ \qquad\textbf{(B)}\ \text{She rounds } a \text{ and } b \text{ up, and she rounds } c \text{down.}\\ \qquad\textbf{(C)}\ \text{She rounds } a \text{ and } c \text{ up, and she rounds } b \text{down.} \\ \qquad\textbf{(D)}\ \text{She rounds } a \text{ up, and she rounds } b \text{ and } c \text{down.}\\ \qquad\textbf{(E)}\ \text{She rounds } c \text{ up, and she rounds } a \text{ and } b \text{down.}$ -/
theorem algebra_96632 (a b c d e f : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (had : a < d) (hbe : b > e) (hfc : f < c) :
    (a / b : ℝ) - c < (d / e : ℝ) - f := by
  -- Prove that d / e (d = rounded up a, e = rounded down b) is greater than a / b
  have h1 : (a : ℝ) / (b : ℝ) < (d : ℝ) / (e : ℝ) := by
    apply div_lt_div₀
    · exact_mod_cast had
    · exact_mod_cast hbe.le
    · exact_mod_cast hd.le
    . exact_mod_cast he
  -- Prove that (a / b) - c < (d / e) - f (f = rounded down c)
  apply sub_lt_sub h1
  exact_mod_cast hfc