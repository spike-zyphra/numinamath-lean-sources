import Mathlib
import Aesop

/-Delilah writes down the positive factors of $12$ on a piece of paper, which she gives to Ezekiel. Next to each factor, Ezekiel writes all of the positive integers that are less than or equal to that number and that share no divisors with the factor other than $1.$ (So, for example, Ezekiel will write $``1"$ next to each of the factors Delilah writes.) How many numbers total does Ezekiel write?-/
theorem algebra_19926 {n : ℕ} (hn : n = 12) :
    ∑ m ∈ n.divisors, {k | 0 < k ∧ k ≤ m ∧ Nat.Coprime k m}.encard = 12 := by
  -- Because n = 12, and 12.divisors = {1, 2, 3, 4, 6, 12}
  have : n.divisors = {1, 2, 3, 4, 6, 12} := by rw [hn]; rfl
  rw [this]
  simp
  -- m = 1, the number of {k | 0 < k ∧ k ≤ 1 ∧ k.Coprime 1} is 1
  -- And, {k | 0 < k ∧ k ≤ 1 ∧ k.Coprime 1} = {k | 0 < k ∧ k ≤ 1}
  have : {k | 0 < k ∧ k ≤ 1}.encard = 1 := by
    have : {k | 0 < k ∧ k ≤ 1} = {1} := by
      ext k
      simp
      omega
    rw [this]
    simp
  rw [this]
  -- m = 2, similar to above
  have : {k | 0 < k ∧ k ≤ 2 ∧ Odd k}.encard = 1 := by
    have : {k | 0 < k ∧ k ≤ 2 ∧ Odd k} = {1} := by
      ext k
      simp
      rw [odd_iff_exists_bit1]
      constructor
      · rintro ⟨hk₁, ⟨hk₂, ⟨p, hp⟩⟩⟩
        omega
      · intro hk
        use (by linarith)
        use (by linarith)
        use 0
        linarith
    rw [this]
    simp
  rw [this]
  -- m = 3
  have : {k | 0 < k ∧ k ≤ 3 ∧ k.Coprime 3}.encard = 2 := by
    have : {k | 0 < k ∧ k ≤ 3 ∧ k.Coprime 3} = {1, 2} := by
      ext k
      simp
      constructor
      · rintro ⟨hk₁, hk₂, hk₃⟩
        by_contra!
        have : k = 3 := by omega
        rw [this] at hk₃
        norm_num at hk₃
      · rintro (r | r)
        repeat rw [r]; exact ⟨by simp, by simp, by rfl⟩
    rw [this]
    apply Set.encard_pair (by linarith)
  rw [this]
  -- m = 4
  have : {k | 0 < k ∧ k ≤ 4 ∧ k.Coprime 4}.encard = 2 := by
    have : {k | 0 < k ∧ k ≤ 4 ∧ k.Coprime 4} = {1, 3} := by
      ext k
      simp
      constructor
      · rintro ⟨hk₁, hk₂, hk₃⟩
        by_contra!
        by_cases h: k ≤ 4
        · interval_cases k <;> norm_num at this hk₃
        linarith
      · rintro (r | r)
        repeat rw [r]; exact ⟨by simp, by simp, by rfl⟩
    rw [this]
    apply Set.encard_pair (by linarith)
  rw [this]
  -- m = 6
  have : {k | 0 < k ∧ k ≤ 6 ∧ k.Coprime 6}.encard = 2 := by
    have : {k | 0 < k ∧ k ≤ 6 ∧ k.Coprime 6} = {1, 5} := by
      ext k
      simp
      constructor
      · rintro ⟨hk₁, hk₂, hk₃⟩
        by_contra!
        by_cases h: k ≤ 6
        · interval_cases k <;> norm_num at this hk₃
        linarith
      · rintro (r | r)
        repeat rw [r]; exact ⟨by simp, by simp, by rfl⟩
    rw [this]
    apply Set.encard_pair (by linarith)
  rw [this]
  -- m = 12
  have : {k | 0 < k ∧ k ≤ 12 ∧ k.Coprime 12}.encard = 4 := by
    have hset : {k | 0 < k ∧ k ≤ 12 ∧ k.Coprime 12} = {1, 5, 7, 11} := by
      ext k
      simp
      constructor
      · rintro ⟨hk₁, hk₂, hk₃⟩
        by_contra!
        by_cases h: k ≤ 12
        · interval_cases k <;> norm_num at this hk₃
        linarith
      · rintro (r | r | r | r)
        repeat rw [r]; exact ⟨by simp, by simp, by rfl⟩
    have : {k | 0 < k ∧ k ≤ 12 ∧ k.Coprime 12}.ncard
         = {k | 0 < k ∧ k ≤ 12 ∧ k.Coprime 12}.encard := by
      apply Set.Finite.cast_ncard_eq
      rw [hset]
      exact Set.toFinite {1, 5, 7, 11}
    rw [this.symm, hset]
    norm_cast
    repeat rw [Set.insert_eq, Set.ncard_union_eq, Set.ncard_singleton]
    rw [Set.ncard_singleton]
    repeat simp
  -- Add up all encard
  rw [this]
  norm_num
