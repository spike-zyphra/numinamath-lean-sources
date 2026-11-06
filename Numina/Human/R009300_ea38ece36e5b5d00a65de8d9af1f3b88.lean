import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Card

/- Find the number of positive integers that are divisors of at least one of 10^10, 15^7, 18^11. -/

theorem AIME_Number_Theory_728 : Nat.card {n : ℕ | n ∣ 10^10 ∨ n ∣ 15^7 ∨ n ∣ 18^11} = 435 := by
  let A := Nat.divisors (10^10)
  let B := Nat.divisors (15^7)
  let C := Nat.divisors (18^11)
  -- We have the following relation between the sets
  have : {n : ℕ | n ∣ 10^10 ∨ n ∣ 15^7 ∨ n ∣ 18^11} = A ∪ B ∪ C := by
    ext n
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h | h
      · left; left; rw [Nat.mem_divisors]; exact ⟨h, by linarith⟩
      · left; right; rw [Nat.mem_divisors]; exact ⟨h, by linarith⟩
      · right; rw [Nat.mem_divisors]; exact ⟨h, by linarith⟩
    · intro h
      rcases h with h | h
      · rcases h with h | h
        · left; rw [Nat.mem_divisors] at h; exact h.left
        · right; left; rw [Nat.mem_divisors] at h; exact h.left
      · right; right; rw [Nat.mem_divisors] at h; exact h.left
  -- We derive the inclusion-exclusion formula
  have inclusion_exclusion (S T : Finset ℕ) : (S ∪ T).card = S.card + T.card - (S ∩ T).card := by
    calc (S ∪ T).card = (S ∪ T).card + (S ∩ T).card - (S ∩ T).card := Nat.eq_sub_of_add_eq rfl
      _ = S.card + T.card - (S ∩ T).card := by rw [Finset.card_union_add_card_inter]
  -- Intersection distributes over union
  have union_inter : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  -- Intersection distributes over intersection
  have inter_inter : (A ∩ C ∩ (B ∩ C)) = A ∩ B ∩ C := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_inter]
    tauto
  -- We need this cast
  have cast (S : Finset ℕ) : S.toSet.toFinset = S := by
    apply Finset.ext
    simp
  -- n divides both a and b if and only if it divides their gcd
  have divisors_gcd (a b : ℕ) (ha : a > 0) (hb : b > 0) :
      (Nat.divisors a) ∩ (Nat.divisors b) = Nat.divisors (Nat.gcd a b) := by
    apply Finset.ext
    intro n
    simp only [Finset.mem_inter]
    rw [Nat.mem_divisors, Nat.mem_divisors, Nat.mem_divisors]
    constructor
    · intro h
      rcases h with ⟨⟨h₁, h₂⟩, ⟨h₃, _⟩⟩
      exact ⟨Nat.dvd_gcd h₁ h₃, Nat.gcd_ne_zero_left h₂⟩
    · intro h
      rcases h with ⟨h₁, _⟩
      constructor
      · constructor
        · exact dvd_trans h₁ (Nat.gcd_dvd_left a b)
        · linarith
      · constructor
        · exact dvd_trans h₁ (Nat.gcd_dvd_right a b)
        · linarith

  -- We compute the cardinality of each set
  have card_A : A.card = 121 := by
    rw [Nat.card_divisors, Nat.factorization_pow, Nat.primeFactors_pow]
    · have : 10 = 2*5 := by norm_num
      rw [this, Nat.factorization_mul, Nat.primeFactors_mul]
      · norm_num
        rw [Finset.prod_union]
        · simp
        · simp
      all_goals linarith
    · linarith
    · linarith
  have card_B : B.card = 64 := by
    rw [Nat.card_divisors, Nat.factorization_pow, Nat.primeFactors_pow]
    · have : 15 = 3*5 := by norm_num
      rw [this, Nat.factorization_mul, Nat.primeFactors_mul]
      · norm_num
        rw [Finset.prod_union]
        · simp
        · simp
      all_goals linarith
    · linarith
    · linarith
  have card_C : C.card = 276 := by
    rw [Nat.card_divisors, Nat.factorization_pow, Nat.primeFactors_pow]
    · have : 18 = 2*3^2 := by norm_num
      have that : 9 = 3^2 := by norm_num
      rw [this, Nat.factorization_mul, Nat.primeFactors_mul]
      · norm_num
        rw [Finset.prod_union, that, Nat.primeFactors_pow, Nat.factorization_pow]
        · norm_num
        · simp
        · simp
      all_goals linarith
    · linarith
    · linarith
  have card_AB : (A ∩ B).card = 8 := by
    rw [divisors_gcd, Nat.card_divisors]
    · simp only [Nat.reducePow, Nat.reduceGcd]
      have : 78125 = 5^7 := by norm_num
      rw [this, Nat.factorization_pow, Nat.primeFactors_pow]
      · norm_num
      · linarith
    · simp
    · linarith
    · linarith
  have card_AC : (A ∩ C).card = 11 := by
    rw [divisors_gcd, Nat.card_divisors]
    · simp only [Nat.reducePow, Nat.reduceGcd]
      have : 1024 = 2^10 := by norm_num
      rw [this, Nat.factorization_pow, Nat.primeFactors_pow]
      · norm_num
      · linarith
    · simp
    · linarith
    · linarith
  have card_BC : (B ∩ C).card = 8 := by
    rw [divisors_gcd, Nat.card_divisors]
    · simp only [Nat.reducePow, Nat.reduceGcd]
      have : 2187 = 3^7 := by norm_num
      rw [this, Nat.factorization_pow, Nat.primeFactors_pow]
      · norm_num
      · linarith
    · simp only [Nat.reducePow, Nat.reduceGcd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    · linarith
    · linarith
  have card_ABC : (A ∩ B ∩ C).card = 1 := by
    rw [divisors_gcd, divisors_gcd, Nat.card_divisors]
    · simp
    · simp
    · simp
    · linarith
    · linarith
    · linarith

  -- We substitute the values and complete the computation
  simp_rw [this, Nat.card_eq_card_toFinset, cast, inclusion_exclusion, union_inter,
    inclusion_exclusion, inter_inter, card_A, card_B, card_C, card_AB, card_AC, card_BC, card_ABC]