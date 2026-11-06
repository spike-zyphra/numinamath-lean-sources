import Mathlib

open Real Set

/- 19. C7 (CZS 3) Let $M$ be the set of real numbers of the form $\frac{m+n}{\sqrt{m^{2}+n^{2}}}$, where $m$ and $n$ are positive integers. Prove that for every pair $x \in M$, $y \in M$ with $x < y$, there exists an element $z \in M$ such that $x < z < y$. -/
theorem algebra_23830 {x y : ℝ} (hx : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ x = (m + n) / sqrt (m ^ 2 + n ^ 2))
    (hy : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ y = (m + n) / sqrt (m ^ 2 + n ^ 2)) (hxy : x < y) :
    ∃ z : ℝ, ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ z = (m + n) / sqrt (m ^ 2 + n ^ 2) ∧ x < z ∧ z < y := by

  -- let us set f = (u+1)/√(1+u^2)
  let f (u: ℝ): ℝ := (u+1)/√(1+u^2)

  have h1: ∀ (m n: ℕ), m > 0 ∧ n > 0 → f (m/n) = (m+n)/√(m^2+n^2) := by
    intro m n
    intro ⟨hm, hn⟩

    -- m/n+1 = (m+n)/n
    have h₁ : (m:ℝ) / n + 1 = (m + n) / (n:ℝ) := by field_simp [hn]

    -- √(1+(m/n)^2) = √(m^2+n^2)/n
    have h₂ : Real.sqrt (1 + (↑m / ↑n) ^ 2) = Real.sqrt (↑m ^ 2 + ↑n ^ 2) / ↑n := by
      field_simp [hn]
      ring_nf

    -- f(m/n) = (m/n+1)/√(1+(m/n)^2)
    simp only [f]

    -- = ((m+n)/n) / (sqrt (m^2+n^2)/n)
    rw [h₁, h₂]
    -- = (m+n)/sqrt(m^2+n^2)
    field_simp [hn]

  -- prove f is strictly decreasing on [1, +∞)
  have h2: StrictAntiOn f (Ici 1) := by

    -- first we show that f^2(x) is strictly decreasing on [1, +∞)
    have h2_1: StrictAntiOn (λ u:ℝ => (u + 1) ^ 2 / (1 + u ^ 2)) (Ici 1) := by
      intro u hu v hv huv
      simp
      -- 1 ≤ u and 1 ≤ v
      rw [mem_Ici] at hu hv

      -- set g(u) = u + 1/u
      let g := λ u:ℝ => u + 1/u

      -- prove g is strictly increasing on [1, +∞)
      have h2_1_2: StrictMonoOn g (Ici 1) := by
        let g' := λ u:ℝ => 1 - 1/u^2

        -- show deriv g = g' = 1 - 1/u^2
        have hg' : ∀ u:ℝ, 1 ≤ u →  HasDerivAt g (g' u) u := by
          intro u hu
          have hg'1 := hasDerivAt_id u
          have h1 : HasDerivAt (fun u : ℝ => u) 1 u := hasDerivAt_id u
          have h2 : HasDerivAt (fun u : ℝ => 1 / u) (-1 / u ^ 2) u := by
            norm_num
            apply HasDerivAt.inv
            · exact hasDerivAt_id u
            · linarith [hu]
          have h_total : HasDerivAt (fun u : ℝ => u + 1 / u) (1 + (-1 / u ^ 2)) u :=
            h1.add h2
          convert h_total using 1
          ring

        -- prove g' > 0 on (1, +∞)
        have hg'_2 : ∀ u:ℝ, 1 < u → g' u > 0 := by
          intro u hu
          simp [g']
          have h1 : 0 < u := by linarith
          have h2 : 1 < u ^ 2 := by nlinarith
          exact inv_lt_one_of_one_lt₀ h2

        apply strictMonoOn_of_deriv_pos
        -- prove [1, +∞) is convex
        . exact convex_Ici 1
        -- prove g u is continuous for u in [1, +∞)
        . apply continuousOn_of_forall_continuousAt
          intro u hu
          exact (hg' u hu).continuousAt
        -- show g' u > 0 for u in (1, +∞)
        intro u hu
        -- u ∈ [1, +∞) -> 1 ≤ u
        rw [interior_Ici, mem_Ioi] at hu
        simp [(hg' u (by linarith)).deriv]
        exact hg'_2 u hu

      -- rewrite (u+1)^2= u^2 + 2u + 1, (v+1)^2= v^2 + 2v + 1
      repeat rw [add_sq] ; simp

      -- rewrite and simp goal to 1 + 2 * u / (u ^ 2 + 1) > 1 + 2 * v / (v ^ 2 + 1)
      rw [add_right_comm (v^2), add_right_comm (u^2)]
      rw [add_div (v^2+1), add_div (u^2+1)]
      norm_num [add_comm]
      repeat rw [div_self]
      any_goals try positivity

      -- simp goal to u+1/u = (u^2+1)/u < (v^2+1)/v = v+1/v
      norm_num
      rw [mul_div_assoc, mul_div_assoc]
      simp
      rw [← one_div_lt_one_div]
      any_goals try positivity
      simp
      repeat rw [add_div]
      simp only [pow_two]
      simp only [mul_self_div_self]

      -- now we can show goal from h2_1_2
      exact (h2_1_2.lt_iff_lt hu hv).mpr huv

    -- prove f is strictly decreasing from f^2 is strictly decreasing
    intro u hu v hv huv
    rw [mem_Ici] at hu hv
    have h2_2 := (h2_1.lt_iff_lt hv hu).mpr huv
    simp [f]
    rw [← sqrt_lt_sqrt_iff] at h2_2 ; any_goals try positivity
    repeat rw [sqrt_div] at h2_2 ; any_goals try positivity
    repeat rw [sqrt_sq_eq_abs] at h2_2
    have h2_3: |v+1| = v+1 := by exact abs_eq_self.mpr (by linarith [hv] )
    have h2_4: |u+1| = u+1 := by exact abs_eq_self.mpr (by linarith [hu] )
    rw [h2_3, h2_4] at h2_2
    exact h2_2

  -- prove that for any x = (m + n) / sqrt (m ^ 2 + n ^ 2) , we can get x = f(m'/n') with m' > n'
  have h3: ∀ (x: ℝ),
      (∃ m n: ℕ, m > 0 ∧ n > 0 ∧ x = (m + n) / sqrt (m ^ 2 + n ^ 2)) →
      (∃ m' n': ℕ, m' > 0 ∧ n' > 0 ∧ (m':ℝ)/n' ≥ 1 ∧ x = f (m'/n')) := by

    intro x ⟨m, n, ⟨hm, hn, hx⟩ ⟩
    by_cases h : m < n
    -- when m < n, we can set m' = n and n' = m
    . apply Exists.intro n
      apply Exists.intro m
      repeat (any_goals constructor)
      -- m' = n > 0
      . exact hn
      -- n' = m > 0
      . exact hm
      -- m'/n' = n/m > 1
      . field_simp
        rw [le_div_iff₀, one_mul]
        simp
        exact le_of_lt h
        simp [hm]
      -- x = (n+m)/sqrt(n^2+m^2) = f(n/m)
      . rw [h1]
        simp [h1, hx, add_comm]
        exact ⟨hn, hm⟩
    . -- when m >= n, we can set m' = m and n' = n
      apply Exists.intro m
      apply Exists.intro n
      repeat (any_goals constructor)
      -- m' = m > 0
      . exact hm
      -- n' = n > 0
      . exact hn
      -- m'/n' = m/n >= 1
      . field_simp
        rw [le_div_iff₀, one_mul]
        simp
        exact le_of_not_lt h
        simp [hn]
      -- x = (m+n)/sqrt(m^2+n^2) = f(m/n)
      . rw [h1]
        simp [h1, hx]
        exact ⟨hm, hn⟩

  -- extract mx/nx/my/ny from hx & hy, with mx > nx and my > ny
  let ⟨mx, nx, hx⟩ := h3 x hx
  let ⟨my, ny, hy⟩ := h3 y hy

  let ux: ℝ := mx / nx
  let uy: ℝ := my / ny

  -- find any value between ux and uy
  let uz: ℝ := (ux+uy)/2
  let z := f uz

  have h4: uz ≥ 1 := by
    have : ux ≥ 1 := by simp [ux, hx.2.2.1]
    have : uy ≥ 1 := by simp [uy, hy.2.2.1]
    simp [uz]
    linarith

  have h5: ∃ m n: ℕ, m > 0 ∧ n > 0 ∧ uz = m/n := by
    -- prove uz = (mx*ny+my*nx)/(2*nx*ny)
    let m := mx*ny+my*nx
    let n := 2*nx*ny
    have h4_1: uz = m/n := by
      simp [uz, m, n, ux, uy]
      have hnx : ↑nx ≠ 0 := by linarith
      have hny: ↑ny ≠ 0 := by linarith
      field_simp [hnx, hny]
      apply Or.inl
      linarith

    -- prove mx*ny+my*nx and 2*nx*ny are a set m n that satisfy the condition
    apply Exists.intro m
    apply Exists.intro n
    repeat (any_goals constructor)
    . simp [m, hx.1, hx.2.1, hy.1, hy.2.1]
    . simp [n, hx.2.1, hy.2.1]
    . exact h4_1

  have h6: uy < uz ∧ uz < ux := by
    rw [hx.2.2.2, hy.2.2.2] at hxy
    -- get uy < ux from x = f(ux) < f(uy) = y
    have huyux: uy < ux := by exact (h2.lt_iff_lt hx.2.2.1 hy.2.2.1).mp hxy
    simp [uz]

    -- get uy < uz ∧ uz < ux from linarith
    constructor <;> linarith

  have ⟨mz, nz, hz⟩ := h5

  -- provide existence of z/mz/nz
  apply Exists.intro z
  apply Exists.intro mz
  apply Exists.intro nz

  -- constructor all goals and finish them one by one
  repeat (any_goals constructor)

  -- have mz > 0
  . exact hz.1

  -- have nz > 0
  . exact hz.2.1

  -- have z = f(uz) = f(mz/nz) = (mz + nz) / sqrt (mz ^ 2 + nz ^ 2)
  . simp only [z, h1 mz nz ⟨hz.1, hz.2.1⟩, hz.2.2]

  -- have ux < uz -> x = f(ux) < f(uz) = z
  . simp only [z, hx.2.2.2]
    exact (h2.lt_iff_lt hx.2.2.1 h4).mpr h6.2

  -- have uz < uy -> z = f(uz) < f(uy) = y
  . simp only [z, hy.2.2.2]
    exact (h2.lt_iff_lt h4 hy.2.2.1).mpr h6.1
