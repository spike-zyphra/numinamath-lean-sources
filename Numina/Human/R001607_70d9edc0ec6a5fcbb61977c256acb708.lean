import Mathlib

/- 21. (CZS 2) Let $a_{0}, a_{1}, \ldots, a_{k}(k \geq 1)$ be positive integers. Find all positive integers $y$ such that  $$ a_{0}\left|y ; \quad\left(a_{0}+a_{1}\right)\right|\left(y+a_{1}\right) ; \ldots ; \quad\left(a_{0}+a_{n}\right) \mid\left(y+a_{n}\right) . $$ -/
theorem Other_24797 {k y : ℕ} (hk: k ≥ 1) (a : ℕ → ℕ)
  (apos: ∀i ∈ Finset.range (k+1), 0 < a i) (ypos: 0 < y)
  {s: Finset ℕ} (hs: s = {m:ℕ | (∃ j ∈ Finset.range (k+1), 0 < j ∧ m = a 0 + a j) ∨ m = a 0}):
  ((a 0 ∣ y) ∧ (∀i ∈ Finset.range (k+1), 0 < i → a 0 + a i ∣ y + a i)) ↔
  ( ∃ k, y = s.lcm id * k + a 0) := by

  constructor <;> intro h

  · -- y ≥ a0, since a0 ∣ y and 0 < y
    have yge := Nat.le_of_dvd ypos h.left
    -- a0 + ai ∣ y + ai, then a0 + ai ∣ (y + ai) - (a0 + ai) = y - a0
    have h1: ∀i ∈ Finset.range (k+1), 0 < i → a 0 + a i ∣ y - a 0 := by
      intro i hi inz
      have hh := h.right i hi inz
      have: y - a 0 = (y + a i) - (a 0 + a i) := by omega
      rw [this]
      refine Nat.dvd_sub' hh dvd_rfl
    -- then lcm of a0, a0+a1, a0+a2, ..., a0 + an divide y - a0
    have h2: s.lcm id ∣ y - a 0 := by
      apply Finset.lcm_dvd ?_
      intro b hb
      simp only [id_eq]
      replace hb: b ∈ (s: Set ℕ) := by simp [hb]
      simp only [hs, Set.mem_setOf_eq] at hb
      rcases hb with hb | hb
      · rcases hb with ⟨j, hj, jnz, beq⟩
        rw [beq]
        exact h1 j hj jnz
      · rw [hb]
        exact Nat.dvd_sub' h.left dvd_rfl
    rcases h2 with ⟨k, hk⟩
    use k
    exact (Nat.sub_eq_iff_eq_add yge).mp hk

  · -- y = a0 + ... ≥ a0
    have yge: y ≥ a 0 := by
      rcases h with ⟨k, hk⟩
      simp [hk]
    -- and lcm divide y - a0
    replace h: s.lcm id ∣ y - a 0 := by
      rcases h with ⟨k, hk⟩
      use k
      exact (Nat.sub_eq_iff_eq_add yge).mpr hk
    -- since lcm divide, then each component divide.
    replace h: ∀b ∈ (s: Set ℕ), b ∣ y - a 0 := by
      rw [Finset.lcm_dvd_iff] at h
      simpa only [Finset.mem_coe, id_eq] using h
    simp only [hs, Set.mem_setOf_eq] at h
    constructor
    · specialize h (a 0)
      simp only [self_eq_add_right, or_true, forall_const] at h
      rw [← Nat.sub_add_cancel yge]
      exact Nat.dvd_add_self_right.mpr h
    · intro i hi inz
      specialize h (a 0 + a i)
      suffices hh: (a 0 + a i) ∣ (y - a 0) by
        have: y + a i = (y - a 0) + (a 0 + a i) := by omega
        rw [this]
        exact Nat.dvd_add_self_right.mpr hh
      apply h
      left
      use i