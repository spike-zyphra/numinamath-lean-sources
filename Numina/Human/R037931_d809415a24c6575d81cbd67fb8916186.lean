import Mathlib

/- The real positive numbers $x, y, z$ satisfy the relations $x \leq 2$, $y \leq 3, x+y+z=11$. Prove that $\sqrt{x y z} \leq 6$. -/
theorem inequalities_605327 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (_ : 0 < z)
    (h1 : x ≤ 2) (h2 : y ≤ 3) (h3 : x + y + z = 11) :
    Real.sqrt (x * y * z) ≤ 6 := by
  -- After the substitutions $x=2-u, y=3-v$ with $u \in[0,2), v \in[0,3)$,
  let u := 2 - x
  let v := 3 - y
  have hu : u ∈ Set.Ico 0 2 := by
    simp [u]
    exact ⟨h1, hx⟩
  have hv : v ∈ Set.Ico 0 3 := by
    simp [v]
    exact ⟨h2, hy⟩
  -- we have $z = 6 + u + v$.
  have hz' : z = 6 + u + v := by
    simp [u, v]
    linear_combination h3
  -- The inequality to prove becomes $\sqrt{(2-u)(3-v)(6+u+v)} \leq 6$.
  suffices h : Real.sqrt ((2 - u) * (3 - v) * (6 + u + v)) ≤ 6
  · simp [←hz', u, v] at h
    exact h
  · -- the required inequality becomes $$ (2-u)(3-v)(6+u+v) \leqslant 36 $$
    apply Real.sqrt_le_left (by norm_num) |>.mpr
    norm_num
    --  write the inequality as $$ (6-u-v)(6+u+v)+(u v-2 u-v)(6+u+v) \leq 36 $$
    suffices h : (6 - u - v) * (6 + u + v) + (u * v - 2 * u - v) * (6 + u + v) ≤ 36
    · calc
        (2 - u) * (3 - v) * (6 + u + v) = (6 - u - v) * (6 + u + v) + (u * v - 2 * u - v) * (6 + u + v) := by ring
        _ ≤ 36 := h
    · -- the first product on the lefthand side is $36-(u+v)^{2} \leq 36$
      have h1 : (6 - u - v) * (6 + u + v) ≤ 36 := by
        calc
          (6 - u - v) * (6 + u + v) = 36 - (u + v) ^ 2 := by ring
          _ ≤ 36 - 0 := by rel [sq_nonneg (u + v)]
          _ = 36 := by simp
      --  it is enough to prove that the second product is nonpositive.
      have h2 : (u * v - 2 * u - v) * (6 + u + v) ≤ 0 := by
        apply mul_nonpos_of_nonpos_of_nonneg
        · have h3 : u * (v - 2) ≤ v := by
            by_cases hv' : v ≤ 2
            · calc
                u * (v - 2) ≤ 0 := by apply mul_nonpos_of_nonneg_of_nonpos hu.left (sub_nonpos.mpr hv')
                _ ≤ v := by exact hv.left
            · simp at hv'
              have : v - 2 ≥ 0 := by apply le_of_lt; exact sub_pos.mpr hv'
              calc
                u * (v - 2) ≤ 2 * (v - 2) := by rel [hu.right, this]
                _ = v + (v - 4) := by ring
                _ ≤ v + 0 := by simp; apply le_of_lt; apply lt_trans hv.right; norm_num
                _ = v := by simp
          rw [mul_sub] at h3
          apply sub_nonpos.mpr
          nth_rw 2 [mul_comm]
          exact h3
        · apply add_nonneg
          · apply add_nonneg (by simp) hu.left
          · exact hv.left
      -- the result follows from the two inequalities above
      calc
        (6 - u - v) * (6 + u + v) + (u * v - 2 * u - v) * (6 + u + v) ≤ 36 + 0 := by rel [h1, h2]
        _ = 36 := by simp
