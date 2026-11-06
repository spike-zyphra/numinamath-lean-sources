import Mathlib

-- Show that 0 < x, 0 < y, 0 < z, and x * y * z = (22 - x) * (22 - y) * (22 - z)
-- imply that x < 22 and y < 22 and z < 22.
lemma lemma_1 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = (22 - x) * (22 - y) * (22 - z)) :
    x < 22 ∧ y < 22 ∧ z < 22 := by
  constructorm* _ ∧ _
  · -- Assume that x ≥ 22 then x * y * z = 0, a contradiction.
    contrapose! h
    simp [show 22 - x = 0 by omega]
    omega
  · -- Assume that y ≥ 22 then x * y * z = 0, a contradiction.
    contrapose! h
    simp [show 22 - y = 0 by omega]
    omega
  · -- Assume that z ≥ 22 then x * y * z = 0, a contradiction.
    contrapose! h
    simp [show 22 - z = 0 by omega]
    omega

-- Show that 0 < x, 0 < y, 0 < z, and x * y * z = (22 - x) * (22 - y) * (22 - z)
-- imply that x = 11 or y = 11 or z = 11.
lemma lemma_2 {x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z = (22 - x) * (22 - y) * (22 - z)) : x = 11 ∨ y = 11 ∨ z = 11 := by
  have ⟨hx1, hy1, hz1⟩ := lemma_1 hx hy hz h
  -- It is enough to show that 11 ∣ 2 * x * y * z.
  suffices h : 11 ∣ 2 * x * y * z by
    -- Indeed, if 11 ∣ 2 * x * y * z then 11 ∣ x or 11 ∣ y or 11 ∣ z (because 11 is prime).
    have hp : Nat.Prime 11 := by norm_num
    simp_rw [hp.dvd_mul] at h
    -- Prove that for any natural t, 0 < t < 22 and 11 ∣ t imply t = 11.
    have h1 {t} (ht0 : 0 < t) (ht1 : t < 22) (ht2 : 11 ∣ t) : t = 11 := by
      -- We have t = 11 * k for some k.
      have ⟨k, hk⟩ := ht2
      -- If k = 0 then t = 0, a contradiction.
      -- If k = 1 then t = 11.
      -- If k ≥ 2 then t ≥ 22, a contradiction.
      rcases show k = 0 ∨ k = 1 ∨ 2 ≤ k by omega with hk | hk | hk <;> linarith
    -- We conclude that x = 11 or y = 11 or z = 11.
    rcases h with (h | h) | h <;> tauto
  -- Show that 11 ∣ 2 * x * y * z.
  zify [hx1, hy1, hz1] at h ⊢
  -- It is enough to show that
  -- 2 * x * y * z = 11 * (2 * 22^2 - 2 * 22 * (x + y + z) + 2 * (x * y + y * z + z * x)).
  use 2 * 22^2 - 2 * 22 * (x + y + z) + 2 * (x * y + y * z + z * x)
  -- This result follows from h.
  linear_combination h

-- Show that 0 < y ≤ z and 11 * y * z = (22 - 11) * (22 - y) * (22 - z)
-- imply that 2 * (y^2 + z^2) = 484 + (z - y)^2.
lemma lemma_3 {y z : ℕ} (hy : 0 < y) (hyz : y ≤ z)
    (h : 11 * y * z = (22 - 11) * (22 - y) * (22 - z)) :
    2 * (y ^ 2 + z ^ 2) = 484 + (z - y)^2 := by
  have ⟨_, hy1, hz1⟩ := lemma_1 (x := 11) (by norm_num) hy (by linarith) h
  -- h implies that y + z = 22.
  replace h : y + z = 22 := by
    zify [hy1, hz1] at h ⊢
    rw [← mul_left_inj' (c := 242) (by norm_num)]
    linear_combination h
  zify [hyz] at h ⊢
  -- We have
  -- 2 * (y^2 + z^2) = (y + z)^2 + (z - y)^2 = 22^2 + (z - y)^2.
  calc
    2 * (y^2 + z^2 : ℤ) = (y + z)^2 + (z - y)^2 := by ring
    _ = 484 + (z - y)^2 := by
      rw [h]
      ring

/- 11. Given positive integers $x, y, z$ satisfying $x y z=(22-x)(22-y)(22-z)$, and $x+y+z<44, x^{2}+y^{2}+z^{2}$, the maximum and minimum values are denoted as $M$ and $N$, respectively, then $M+N=$ $\qquad$. -/
theorem algebra_294975 (m n : ℕ)
    (hmin : IsLeast {s | ∃ x y z, s = x^2 + y^2 + z^2 ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z = (22 - x) * (22 - y) * (22 - z) ∧ x + y + z < 44} n)
    (hmax : IsGreatest {s | ∃ x y z, s = x^2 + y^2 + z^2 ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧ x * y * z = (22 - x) * (22 - y) * (22 - z) ∧ x + y + z < 44} m) :
    m + n = 926 := by
  set p := {s | _}
  -- Show that the set from the theorem statement is equal to
  -- {s | ∃ y z, 2 * s = 2 * 11^2 + 484 + (z - y)^2 ∧ 0 < y ∧ y ≤ z ∧ 11 * y * z = (22 - 11) * (22 - y) * (22 - z) ∧ 11 + y + z < 44}.
  have hp_eq : p = {s | ∃ y z, 2 * s = 2 * 11^2 + 484 + (z - y)^2 ∧ 0 < y ∧ y ≤ z ∧ 11 * y * z = (22 - 11) * (22 - y) * (22 - z) ∧ 11 + y + z < 44} := by
    ext s
    simp only [Set.mem_setOf_eq, p]
    constructor
    · intro ⟨x, y, z, hs, hx, hy, hz, h, h1⟩
      -- Assume that 0 < x, 0 < y, 0 < z, s = x^2 + y^2 + z^2,
      -- x * y * z = (22 - x) * (22 - y) * (22 - z), and x + y + z < 44.
      -- Show that there exists y' z' such that
      -- 2 * s = 2 * 11^2 + 484 + (z' - y')^2, 0 < y' ≤ z', and 11 + y' + z' < 44.
      -- lemma_2 implies that x = 11 or y = 11 or z = 11.
      rcases lemma_2 hx hy hz h with heq | heq | heq
      · -- Assume that x = 11.
        -- Without loss of generality, assume that y ≤ z.
        wlog hyz : y ≤ z generalizing y z
        · simp at hyz
          exact this z y (by linarith) hz hy (by linarith) (by linarith) (le_of_lt hyz)
        subst x
        -- lemma_3 implies that 2 * (y^2 + z^2) = 484 + (z - y)^2.
        have h3 := lemma_3 hy hyz h
        use y, z, by linarith
      · -- Assume that y = 11.
        -- Without loss of generality, assume that x ≤ z.
        wlog hxz : x ≤ z generalizing x z
        · simp at hxz
          exact this z x (by linarith) hz hx (by linarith) (by linarith) (le_of_lt hxz)
        subst y
        -- lemma_3 implies that 2 * (x^2 + z^2) = 484 + (z - x)^2.
        have h3 := lemma_3 hx hxz (by linarith)
        use x, z, by linarith, hx, hxz, by linarith, by linarith
      · -- Assume that z = 11.
        -- Without loss of generality, assume that x ≤ y.
        wlog hxy : x ≤ y generalizing x y
        · simp at hxy
          exact this y x (by linarith) hy hx (by linarith) (by linarith) (le_of_lt hxy)
        subst z
        -- lemma_3 implies that 2 * (x^2 + y^2) = 484 + (y - x)^2.
        have h3 := lemma_3 hx hxy (by linarith)
        use x, y, by linarith, hx, hxy, by linarith, by linarith
    · intro ⟨y, z, hs, hy, hyz, h, h1⟩
      have h3 := lemma_3 hy hyz h
      use 11, y, z, by linarith, by norm_num, hy, by linarith
  -- It is enough to show that IsLeast p 363 and IsGreatest p 563.
  suffices h : IsLeast p 363 ∧ IsGreatest p 563 by
    rw [hmax.unique h.2, hmin.unique h.1]
  constructor
  · -- Prove IsLeast p 363.
    simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, and_imp, hp_eq]
    constructor
    · -- Show that y = 11, z = 11 yield s = 363.
      use 11, 11
      norm_num
    intro s ⟨y, z, hs, hy, hyz, h, h1⟩
    -- We have 2 * s = 2 * 11^2 + 484 + (z - y)^2.
    -- s is minimal when z = y, so 2 * s ≥ 2 * 11^2 + 484 = 726 = 2 * 363.
    nlinarith
  · -- Prove IsGreatest p 563
    simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, and_imp, hp_eq]
    constructor
    · -- Show that y = 1, z = 21 yield s = 563.
      use 1, 21
      norm_num
    intro s ⟨y, z, hs, hy, hyz, h, h1⟩
    -- We have 2 * s = 2 * 11^2 + 484 + (z - y)^2.
    -- Moreover, lemma_1 implies that y < 22 and z < 22.
    have ⟨_, hy, hz⟩ := lemma_1 (x := 11) (z := z) (by norm_num) hy (by linarith) h
    -- It is enough to show that (z - y)^2 ≤ 20^2.
    suffices (z - y)^2 ≤ 20^2 by linarith
    -- It is enough to show that z - y ≤ 20.
    rw [sq_le_sq₀ (by omega) (by norm_num)]
    -- z - y ≤ 21 - 1 = 20 (because z < 22 and y > 0).
    omega