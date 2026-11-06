import Mathlib

open Finset

/- Let $a, b, c$ be positive real numbers such that $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}=a+b+c$. Prove that  $$ \frac{1}{(2 a+b+c)^{2}}+\frac{1}{(2 b+c+a)^{2}}+\frac{1}{(2 c+a+b)^{2}} \leq \frac{3}{16} $$ -/
theorem inequalities_23797 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 1 / c = a + b + c) :
    1 / (2 * a + b + c) ^ 2 + 1 / (2 * b + c + a) ^ 2 + 1 / (2 * c + a + b) ^ 2 ≤ 3 / 16 := by

  -- For positive real numbers x,y,z, by the AM-GM inequality, we obtain 1 / ((2 * x + y + z)^2) ≤ 1 / (4 * (x+y)*(x+z))
  have t (x y z : ℝ) (xpos : 0 < x) (ypos : 0 < y) (zpos : 0 < z) : 1 / ((2*x + y + z)^2) ≤ 1 / (4 * (x+y)*(x+z)) := by
    apply one_div_le_one_div_of_le
    positivity
    have l := two_mul_le_add_sq (x + y) (x + z)
    ring_nf at l
    ring_nf
    linarith

  have t1 := t a b c (by positivity) (by positivity) (by positivity)
  have t2 := t b c a (by positivity) (by positivity) (by positivity)
  have t3 := t c a b (by positivity) (by positivity) (by positivity)

  -- Applying this to the LHS of the inequality to prove, we have [LHS] ≤ (a + b + c) / (2 * (a + b) * (a + c) * (b + c))
  have h1 := calc
    1 / (2 * a + b + c) ^ 2 + 1 / (2 * b + c + a) ^ 2 + 1 / (2 * c + a + b) ^ 2 ≤ 1 / (4 * (a + b) * (a + c)) + 1 / (4 * (b + c) * (b + a)) + 1 / (4 * (c + a) * (c + b)) := add_le_add_three t1 t2 t3
    _ = (a + b + c) / (2 * (a + b) * (a + c) * (b + c)) := by
      field_simp
      ring

  clear t1 t2 t3

  -- Second application of AM-GM

  let w : Fin 6 → ℝ := fun _ => (1:ℝ)/6

  let f : Fin 6 → ℝ := fun i =>
    match i with
    | 0 => a^2 * b
    | 1 => a^2 * c
    | 2 => b^2 * a
    | 3 => b^2 * c
    | 4 => c^2 * a
    | 5 => c^2 * b

  have h2 := Real.geom_mean_le_arith_mean_weighted {0, 1, 2, 3, 4, 5} w f (by
    intro _ _
    positivity
  ) (by
    simp
    norm_num
  ) (by
    intro i _
    fin_cases i <;> positivity
  )

  simp at h2
  unfold w at h2
  unfold f at h2
  dsimp at h2
  norm_num at h2

  repeat rw [←Real.mul_rpow (by positivity) (by positivity)] at h2

  rw [
    show (a ^ 2 * b * (a ^ 2 * c * (b ^ 2 * a * (b ^ 2 * c * (c ^ 2 * a * (c ^ 2 * b)))))) = (a * b * c)^6 by ring
  ] at h2

  rw [show ((a*b*c) ^ 6) ^ ((1:ℝ) / 6) = (a*b*c) by
    rw [show (a*b*c) ^ 6 = ((a*b*c) ^ 2)^3 by ring]
    rw [show ((a*b*c) ^ 2)^3 = ((a*b*c) ^ (2:ℝ))^(3:ℝ) by norm_cast]
    repeat rw [←Real.rpow_mul (by positivity)]
    norm_num
  ] at h2

  -- Second application of AM-GM yields this
  have h3 : 6 * a * b * c ≤
  (a ^ 2 * b) +
    ((a ^ 2 * c) + ((b ^ 2 * a) + ((b ^ 2 * c) + ((c ^ 2 * a) + (c ^ 2 * b))))) := by linarith

  clear w f h2

  -- Or, equivalently this
  have h4 : 8 * (a + b + c) * (a*b + b*c + c*a) ≤ 9 * (a + b) * (b + c) * (c + a) := by
    linarith

  -- We will need h4 in the form []/[] ≤ 9/8 later
  have h4' : (a + b + c) * (a*b + b*c + c*a) / ((a + b) * (b + c) * (c + a)) ≤ ((9:ℝ) / 8) := by
    rw [←mul_le_mul_iff_of_pos_left (show 0 < ((a + b) * (b + c) * (c + a)) by positivity)]
    field_simp
    linarith

  -- the supposition...
  have h5 : a * b + b * c + c * a = a * b * c * (a + b + c) := by
    field_simp at h
    ring_nf at h
    linarith

  -- We need this in fraction form
  have h5' : (a * b + b * c + c * a)  / ((a * b * c * (a + b + c))) = 1 := by
    rw [←h5]
    field_simp

  have l1 := two_mul_le_add_sq (a*b) (b*c)
  have l2 := two_mul_le_add_sq (b*c) (c*a)
  have l3 := two_mul_le_add_sq (c*a) (a*b)

  -- Apply 2-term AM-GM three times to get this
  have h6 : a^2 * b * c + a * b^2 * c + a * b * c^2 ≤ a^2 * b^2 + b^2 * c^2 + c^2 * a^2 := by linarith

  clear l1 l2 l3

  -- Which is equivalent to this
  have h7 : 3*a*b*c*(a+b+c) ≤ (a*b + b*c + c*a)^2 := by linarith

  -- In fraction form
  have h7' : (a*b*c*(a+b+c)) / (a*b + b*c + c*a)^2 ≤ (1/3) := by
    rw [←mul_le_mul_iff_of_pos_left (show 0 < (a*b + b*c + c*a)^2 by positivity)]
    field_simp
    linarith
  clear h6

  have h_final := calc
    (a + b + c) / (2 * (a + b) * (a + c) * (b + c)) = (a + b + c) / (2 * (a + b) * (a + c) * (b + c)) := rfl
    _ = ((a + b + c) * (a*b + b*c + c*a) / ((a + b) * (a + c) * (b + c))) * (((a*b + b*c + c*a) / (a*b*c*(a + b + c))) * (a*b*c*(a + b + c) / ((a*b + b*c + c*a))^2) * (1:ℝ)/2) := by
      field_simp
      ring
    _ ≤ ((9:ℝ)/8) * (((a*b + b*c + c*a) / (a*b*c*(a + b + c))) * (a*b*c*(a + b + c) / ((a*b + b*c + c*a))^2) * (1:ℝ)/2) := by
      -- First estimate, 9/8 is an upper bound for the first term
      gcongr ?_ * _
      rw [show ((a + b) * (a + c) * (b + c)) = ((a + b) * (b + c) * (c + a)) by ring]
      exact h4'
    _ = ((a*b + b*c + c*a) / (a*b*c*(a + b + c))) * ((a*b*c*(a + b + c) / ((a*b + b*c + c*a))^2) * (9:ℝ)/16) := by
      field_simp
      ring
    _ = 1 * ((a*b*c*(a + b + c) / ((a*b + b*c + c*a))^2) * (9:ℝ)/16) := by
      congr
    _ = (a*b*c*(a + b + c) / ((a*b + b*c + c*a))^2) * (9:ℝ)/16 := by
      ring
    _ ≤ (1/3) * (9:ℝ)/16 := by
      gcongr
    _ = 3/16 := by norm_num

  -- combine h1 with h_final
  linarith
