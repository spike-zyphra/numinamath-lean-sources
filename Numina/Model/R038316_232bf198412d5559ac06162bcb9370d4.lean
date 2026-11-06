import Mathlib


lemma lemma_1 (x y z : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (hxy : x ≠ y) (hyz : y ≠ z) (hzx : z ≠ x)
    (hdiv : (x : ℤ) ∣ y ∧ y ∣ z) (h1 : x < 10) (h2 : y < 10) (h3 : z < 10) :
    x ≤ 2 := by
  rcases hdiv with ⟨hdiv1, hdiv2⟩
  have h4 : x ≤ 9 := by omega
  have h5 : y ≤ 9 := by omega
  have h6 : z ≤ 9 := by omega
  interval_cases x <;> try {
    omega
  }
  <;> try {
    interval_cases y <;> try {
      omega
    } <;> try {
      interval_cases z <;> norm_num at hdiv1 hdiv2 h1 h2 h3 hx hy hz hxy hyz hzx
      <;> omega
    }
  }


theorem number_theory_23090 :
    Set.ncard { 100 * x + 10 * y + z | (x : ℕ) (y : ℕ) (z : ℕ) (_ : 1 ≤ x) (_ : x ≤ 9) (_ : 1 ≤ y) (_ : y ≤ 9) (_ : 1 ≤ z) (_ : z ≤ 9) (_ : x ∣ y) (_ : y ∣ z) (_ : x ≠ y ∧ y ≠ z ∧ x ≠ z) } = 7 := by
  have h1 : { 100 * x + 10 * y + z | (x : ℕ) (y : ℕ) (z : ℕ) (_ : 1 ≤ x) (_ : x ≤ 9) (_ : 1 ≤ y) (_ : y ≤ 9) (_ : 1 ≤ z) (_ : z ≤ 9) (_ : x ∣ y) (_ : y ∣ z) (_ : x ≠ y ∧ y ≠ z ∧ x ≠ z) } = { 124, 126, 128, 136, 139, 148, 248 } := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if n is in the left side, it must be in the right side
      rintro ⟨x, y, z, hx1, hx2, hy1, hy2, hz1, hz2, hdiv1, hdiv2, hne, rfl⟩
      have h1 : x ≤ 9 := by linarith
      have h2 : y ≤ 9 := by linarith
      have h3 : z ≤ 9 := by linarith
      interval_cases x <;> try { 
        omega
      } <;> try { 
        interval_cases y <;> try { 
          omega
        } <;> try { 
          interval_cases z <;> norm_num at *
          <;> omega 
        }
      }
    · -- Second direction: if n is in the right side, it must be in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 124
        use 1, 2, 4
        all_goals norm_num
      · -- n = 126
        use 1, 2, 6
        all_goals norm_num
      · -- n = 128
        use 1, 2, 8
        all_goals norm_num
      · -- n = 136
        use 1, 3, 6
        all_goals norm_num
      · -- n = 139
        use 1, 3, 9
        all_goals norm_num
      · -- n = 148
        use 1, 4, 8
        all_goals norm_num
      · -- n = 248
        use 2, 4, 8
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide