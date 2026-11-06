import Mathlib

/-- Auxiliary lemma : for real number $x$, $y$, $z$, if $x^2 + y^2 + z^2 = 0$, 
  then $x =0$ and $y=0$. -/
lemma p2add0 (x y z : ℝ): x ^ 2 + y ^ 2 + z ^ 2 = 0 → x = 0 ∧ y = 0 := by
  intro h
  have h1 : x ^ 2 ≥ 0 := pow_two_nonneg x
  have h4 : y ^ 2 ≥ 0 := pow_two_nonneg y
  have h5 : z ^ 2 ≥ 0 := pow_two_nonneg z
  have : x ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by linarith
  have : y ^ 2 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by linarith
  have h2 : x ^ 2 ≤ 0 := by linarith
  have h3 : y ^ 2 ≤ 0 := by linarith
  exact ⟨pow_eq_zero (le_antisymm h2 h1), pow_eq_zero (le_antisymm h3 h4)⟩

/-- Determine all real number triples $\((a, b, c)\)$ such that the following system of equations has a solution different from $\(x = y = z = 0\)$ :

$$
\begin{aligned}
& a x + b y + c z = 0 \\
& b x + c y + a z = 0 \\
& c x + a y + b z = 0
\end{aligned}
$$-/
theorem linear_algebra_4228 (x y z a b c : ℝ)(A : Matrix (Fin 3) (Fin 3) ℝ)(v : Fin 3 → ℝ)
(hA : A = !![a,b,c;b,c,a;c,a,b]) (_ : v = ![x,y,z]) (hVn0: v ≠ 0)
(heq : Matrix.mulVec A v = 0): a + b + c = 0 ∨ (a = b ∧ b = c) := by
-- the determinant of A equal zero.
have t1 : A.det = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp; use v
rw [hA, Matrix.det_fin_three] at t1; simp at t1
have : (a + b + c) * (a * b + b * c + c * a - a ^ 2 - b ^ 2 - c ^ 2) =
a * c * b - a * a * a - b * b * b + b * a * c + c * b * a - c * c * c := by ring
rw [← this] at t1; simp at t1; cases t1 with
| inl h => left; exact h
| inr h => right;
           have t2 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 
           - 2 * (a * b + b * c + c * a - a ^ 2 - b ^ 2 - c ^ 2) := by ring
           rw [h] at t2; simp at t2
           have := p2add0 (a - b) (b - c) (c - a) t2
           exact ⟨sub_eq_zero.mp this.left, sub_eq_zero.mp this.right⟩