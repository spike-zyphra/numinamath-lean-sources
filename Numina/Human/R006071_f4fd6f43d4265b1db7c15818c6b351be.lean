import Mathlib
open Nat Real Finset Set 

/-Exhibit a set $S$ which tiles the integers $\mathbf{Z}$ but not the natural numbers $\mathbf{N}$.-/
theorem number_theory_612345 :
  ∃ S : Set ℤ, (∃ T : Set ℤ, ∀ z : ℤ, ∃! t : ℤ, ∃ s ∈ S, z = s + t ∧ t ∈ T) ∧
  ¬∃ T : Set ℕ, ∀ n : ℕ, ∃! t : ℕ, ∃ s ∈ S, n = s + t ∧ t ∈ T := by
  -- 定义集合 S = {1, 3, 4, 6}
  let S : Set ℤ := {1, 3, 4, 6}
  use S
  constructor
  · -- Prove that $S$ tiles $Z$.
    -- Prove that the elements of $S$ are distinct modulo $4$.
    have h_distinct_mod_4 : ∀ a ∈ S, ∀ b ∈ S, a % 4 = b % 4 → a = b := by
      intros a ha b hb h_mod
      simp [S] at ha hb
      rcases ha with (rfl | rfl | rfl | rfl) <;> rcases hb with (rfl | rfl | rfl | rfl)
      · rfl
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · rfl
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · rfl
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · norm_num at h_mod
      · rfl
    -- Define the translation set $T$ as multiples of $4$.
    let T : Set ℤ := {t | ∃ k : ℤ, t = 4 * k}
    use T
    intro z
    -- Prove there exists a unique $t ∈ T$ such that $z = s + t$, $s ∈ S$.
    have h_exists : ∃ t : ℤ, ∃ s ∈ S, z = s + t ∧ t ∈ T := by
      let k : ℤ := z / 4
      let r : ℤ := z % 4
      have h_z : z = 4 * k + r ∧ 0 ≤ r ∧ r < 4 := by
        refine ⟨?_, Int.emod_nonneg z (by norm_num), Int.emod_lt_of_pos z (by norm_num)⟩
        rw [← Int.ediv_add_emod z 4]
      have h_r : r = 1 ∨ r = 0 ∨ r = 2 ∨ r = 3 := by
        rcases h_z with ⟨_, h_r_ge, h_r_lt⟩
        interval_cases r
        · right; left; rfl
        · left; rfl
        · right; right; left; rfl
        · right; right; right; rfl
      rcases h_r with (h_r1 | h_r0 | h_r2 | h_r3)
      · use 4 * k, 1
        constructor
        · simp [S]
        · constructor
          · rw [h_z.1, h_r1]
            ring
          · simp [T]
      · use 4 * k - 4, 4
        constructor
        · simp [S]
        · constructor
          · rw [h_z.1, h_r0]
            ring
          · simp [T]; use k - 1; ring
      · use 4 * k - 4, 6
        constructor
        · simp [S]
        · constructor
          · rw [h_z.1,h_r2]
            ring
          · simp [T]; use k - 1; ring
      · use 4 * k, 3
        constructor
        · simp [S]
        · constructor
          · rw [h_z.1,h_r3]
            ring
          · simp [T]
    -- Prove the uniqueness of $t$.
    have h_unique : ∀ t1 t2 : ℤ, (∃ s1 ∈ S, z = s1 + t1 ∧ t1 ∈ T) →
                                   (∃ s2 ∈ S, z = s2 + t2 ∧ t2 ∈ T) → t1 = t2 := by
      intros t1 t2 h1 h2
      rcases h1 with ⟨s1, hs1, hz1, ht1⟩
      rcases h2 with ⟨s2, hs2, hz2, ht2⟩
      simp [T] at ht1 ht2
      rcases ht1 with ⟨k1, rfl⟩
      rcases ht2 with ⟨k2, rfl⟩
      have h_mod : (s1 - s2) = 4 * (k2 - k1) := by linarith
      have h_mod_4 : s1 % 4 = s2 % 4 := by
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        rw [h_mod]
        norm_num
      have h_s1_s2 : s1 = s2 := h_distinct_mod_4 s1 hs1 s2 hs2 h_mod_4
      rw [h_s1_s2] at h_mod
      have h_k : 4 * (k2 - k1) = 0 := by rw [← h_mod]; simp
      have h_k_eq : 4 * k1 = 4 * k2 := by omega
      exact h_k_eq
    rcases h_exists with ⟨t, ht⟩
    use t, ht
    intro t2 ht2
    exact h_unique t2 t ht2 ht
  · -- Prove that $S$ does not tile $N$.
    rintro ⟨T, hT⟩
    -- Check $n = 1$.
    have h_n1 : ∃! t : ℕ, ∃ s ∈ S, 1 = s + t ∧ t ∈ T := by apply hT 1
    rcases h_n1 with ⟨t1, ⟨s1, hs1, h_eq1, ht1⟩, h_unique1⟩
    have h_s1_t1 : s1 = 1 ∧ t1 = 0 := by
        simp [S] at hs1
        have h_s1 : s1 = 1 := by omega
        rw [h_s1] at h_eq1
        have h_t1 : t1 = 0 := by linarith [h_eq1]
        omega
    have h_t1 : t1 = 0 := by linarith [h_eq1]
    have h_t1_in_T : 0 ∈ T := by rw [← h_t1];exact ht1
    -- Check $n = 2$.
    have h_n2 : ∃! t : ℕ, ∃ s ∈ S, 2 = s + t ∧ t ∈ T := by apply hT 2
    rcases h_n2 with ⟨t2, ⟨s2, hs2, h_eq2, ht2⟩, h_unique2⟩
    have h_s2_t2 : s2 = 1 ∧ t2 = 1 := by
        simp [S] at hs2
        have h_s2 : s2 = 1 := by omega
        rw [h_s2] at h_eq2
        have h_t2 : t2 = 1 := by linarith [h_eq2]
        omega
    have h_t2 : t2 = 1 := by linarith [h_eq2]
    have h_t2_in_T : 1 ∈ T := by rw [← h_t2];exact ht2
    -- Check $n = 4$.
    have h_n4 : ∃! t : ℕ, ∃ s ∈ S, 4 = s + t ∧ t ∈ T := by apply hT 4
    rcases h_n4 with ⟨t4, ⟨s4, hs4, h_eq4, ht4⟩, h_unique4⟩
    -- Show two representations for $n = 4$.
    have h_rep1 : ∃ s ∈ S, 4 = s + 0 ∧ 0 ∈ T := by
      use 4
      constructor
      · simp [S]
      · constructor
        · rfl
        · exact h_t1_in_T
    have h_rep2 : ∃ s ∈ S, 4 = s + 1 ∧ 1 ∈ T := by
      use 3
      constructor
      · simp [S]
      · constructor
        · rfl
        · exact h_t2_in_T
    -- Prove that the two representations lead to a contradiction.
    have h_unique_violation : ¬(∃! t : ℕ, ∃ s ∈ S, 4 = s + t ∧ t ∈ T) := by
      intro h_unique
      rcases h_rep1 with ⟨s1, hs1, h_eq1, ht1⟩
      rcases h_rep2 with ⟨s2, hs2, h_eq2, ht2⟩
      have h_t0 : ∃ s ∈ S, 4 = s + 0 ∧ 0 ∈ T := ⟨s1, hs1, h_eq1, ht1⟩
      have h_t1 : ∃ s ∈ S, 4 = s + 1 ∧ 1 ∈ T := ⟨s2, hs2, h_eq2, ht2⟩
      have h_t0_unique : 0 = t4 := by
        apply h_unique4 0
        exact h_t0
      have h_t1_unique : 1 = t4 := by
        apply h_unique4 1
        exact h_t1
      have h_conflict : 0 = 1 := by rw [h_t0_unique, h_t1_unique]
      contradiction
    -- Reconstruct the uniqueness statement using $t4$ and $h_unique4$.
    have h_n4_reconstructed : ∃! t : ℕ, ∃ s ∈ S, 4 = s + ↑t ∧ t ∈ T := by
      use t4
      constructor
      · exact ⟨s4, hs4, h_eq4, ht4⟩
      · exact h_unique4
    -- Verify the uniqueness contradiction.
    exact h_unique_violation h_n4_reconstructed
