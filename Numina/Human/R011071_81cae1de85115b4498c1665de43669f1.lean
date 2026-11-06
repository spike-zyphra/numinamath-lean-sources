import Mathlib

/- $4-$ [ Factorization $]$

Prove that the system of inequalities


$$

\begin{aligned}
& |x|>|y-z+t|, \\
& |y|>|x-z+t|, \\
& |z|>|x-y+t|, \\
& |t|>|x-y+z|
\end{aligned}

$$


has no solutions. -/
theorem inequalities_227706 :
    ¬∃ x y z t : ℝ, |y - z + t| < |x| ∧ |x - z + t| < |y| ∧ |x - y + t| < |z| ∧ |x - y + z| < |t|
  := by
    -- Suppose it has solutions
    by_contra h
    obtain ⟨x, y, z, t, h1, h2, h3, h4⟩ := h

    -- Square equations, remove abs
    replace h1 := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h1
    replace h2 := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h2
    replace h3 := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h3
    replace h4 := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr h4
    simp only [sq_abs] at h1 h2 h3 h4

    -- Create expressions which are all less than 0
    apply_fun (fun a : ℝ => a - x ^ 2) at h1 using StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-x ^ 2)
    apply_fun (fun a : ℝ => a - y ^ 2) at h2 using StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-y ^ 2)
    apply_fun (fun a : ℝ => a - z ^ 2) at h3 using StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-z ^ 2)
    apply_fun (fun a : ℝ => a - t ^ 2) at h4 using StrictMono.add_const (fun ⦃a b⦄ a ↦ a) (-t ^ 2)
    let c1 := (y - z + t - x) * (y - z + t + x)
    let c2 := (x - z + t - y) * (x - z + t + y)
    let c3 := (x - y + t - z) * (x - y + t + z)
    let c4 := (x - y + z - t) * (x - y + z + t)
    convert_to c1 < 0 at h1 <;> ring_nf
    convert_to c2 < 0 at h2 <;> ring_nf
    convert_to c3 < 0 at h3 <;> ring_nf
    convert_to c4 < 0 at h4 <;> ring_nf

    -- Then the product of them all is positive
    have pos : 0 < c1*c2*c3*c4
    · convert_to 0 < (c1 * c2) * (c3 * c4)
      exact mul_assoc (c1 * c2) c3 c4
      refine mul_pos ?_ ?_
      exact mul_pos_of_neg_of_neg h1 h2
      exact mul_pos_of_neg_of_neg h3 h4

    -- But we also know that the product of them all is the product of
    -- four squares times -1
    have four_eq : c1 * c2 * c3 * c4
      = -(((x - y + z - t) ^ 2 * (x + y - z + t) ^ 2) * (x - y + z + t) ^ 2 * (x - y - z  + t) ^ 2)
      := by ring

    -- So it's less than or equal to 0
    have neg : c1*c2*c3*c4 ≤ 0
    · rw [four_eq, Left.neg_nonpos_iff]
      positivity

    -- Contradiction
    exact absurd neg <| not_le_of_lt pos