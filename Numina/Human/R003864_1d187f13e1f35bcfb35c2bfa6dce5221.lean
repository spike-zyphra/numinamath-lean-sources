import Mathlib
/- Let $a, b, c$ be three distinct numbers, and let the following equations hold for them:


$$

\begin{aligned}
& a^{3}+p a+q=0 \\
& b^{3}+p b+a=0 \\
& c^{3}+p c+q=0
\end{aligned}

$$


Prove that $a+b+c=0$. -/
theorem algebra_217209 {a b c p q : ℝ} (ha : a^3 + p * a + q = 0) (hb : b^3 + p * b + q = 0)
    (hc : c^3 + p * c + q = 0) (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    a + b + c = 0 := by
  --Obtain the following.
  have h1 : a^3 + p * a + q = 0 := ha
  have h2 : b^3 + p * b + q = 0 := hb
  have h3 : c^3 + p * c + q = 0 := hc
  have hab : a ≠ b := habc.1
  have hac : a ≠ c := habc.2.1
  have hbc : b ≠ c := habc.2.2
  --Subtracting h1 and h2 gives.
  have eq1 : a^3 + p * a + q - (b^3 + p * b + q) = 0 := by linarith
  --Subtracting h1 and h2 gives.
  have eq2 : (a - b) * (a^2 + a * b + b^2 + p) = 0 := by
    ring_nf at eq1 ⊢
    linarith
  --Obtian the gollowing as a ≠ b.
  have h4 : a^2 + a * b + b^2 + p = 0 := by
    apply_fun (λ x => x / (a - b)) at eq2
    field_simp [sub_ne_zero.mpr hab] at eq2
    linarith
  --Show a^3 + p * a + q - (c^3 + p * c + q) = 0.
  have eq3 : a^3 + p * a + q - (c^3 + p * c + q) = 0 := by linarith
  --Factor out a - c.
  have eq4 : (a - c) * (a^2 + a * c + c^2 + p) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  --Since a ≠ c, obtain a^2 + a * c + c^2 + p = 0.
  have h5 : a^2 + a * c + c^2 + p = 0 := by
    apply_fun (λ x => x / (a - c)) at eq4
    field_simp [sub_ne_zero.mpr hac] at eq4
    linarith
  --Obtain a * b - a * c + b^2 - c^2 = 0 by subtracting.
  have eq5 : a * b - a * c + b^2 - c^2 = 0 := by linarith
  --Factorize.
  have eq6 : a * (b - c) + (b + c) * (b - c) = 0 := by linarith
  --Factorize.
  have eq7 : (a + b + c ) * (b - c) = 0 := by linarith
  --Obtain the following.
  have h5 : a + b + c = 0 ∨ b - c = 0 := by exact mul_eq_zero.mp eq7
  --Since b - c ≠ 0, a + b + c = 0.
  have h6 : b - c ≠ 0 := by
    intro h
    have : b = c := by linarith
    contradiction
  tauto