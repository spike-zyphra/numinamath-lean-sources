import Mathlib

theorem number_theory_3466 : ∑ᶠ x ∈ {x | ∃n, 100 ∣ n ∧ x = n % 96}, x = 1104 := by
  have h1 : {x | ∃n, 100 ∣ n ∧ x = n % 96} = {0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x is a remainder of a multiple of 100 divided by 96, then x is in the set.
      rintro ⟨n, hn, hx⟩
      have h100 : 100 ∣ n := hn
      rcases h100 with ⟨k, hk⟩
      have h2 : x = (100 * k) % 96 := by
        rw [show n = 100 * k by linarith [hk]] at hx
        omega
      have h3 : x % 4 = 0 := by
        rw [h2]
        omega
      have h4 : x ≤ 95 := by
        rw [h2]
        omega
      omega
    · -- Second direction: if x is in the set, then x is a possible remainder.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 0
        use 0
        all_goals norm_num
      · -- x = 4
        use 100
        all_goals norm_num
      · -- x = 8
        use 200
        all_goals norm_num
      · -- x = 12
        use 300
        all_goals norm_num
      · -- x = 16
        use 400
        all_goals norm_num
      · -- x = 20
        use 500
        all_goals norm_num
      · -- x = 24
        use 600
        all_goals norm_num
      · -- x = 28
        use 700
        all_goals norm_num
      · -- x = 32
        use 800
        all_goals norm_num
      · -- x = 36
        use 900
        all_goals norm_num
      · -- x = 40
        use 1000
        all_goals norm_num
      · -- x = 44
        use 1100
        all_goals norm_num
      · -- x = 48
        use 1200
        all_goals norm_num
      · -- x = 52
        use 1300
        all_goals norm_num
      · -- x = 56
        use 1400
        all_goals norm_num
      · -- x = 60
        use 1500
        all_goals norm_num
      · -- x = 64
        use 1600
        all_goals norm_num
      · -- x = 68
        use 1700
        all_goals norm_num
      · -- x = 72
        use 1800
        all_goals norm_num
      · -- x = 76
        use 1900
        all_goals norm_num
      · -- x = 80
        use 2000
        all_goals norm_num
      · -- x = 84
        use 2100
        all_goals norm_num
      · -- x = 88
        use 2200
        all_goals norm_num
      · -- x = 92
        use 2300
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> try { native_decide }