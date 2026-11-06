import Mathlib.Tactic
import Mathlib.Util.Delaborators
import Mathlib.Data.Set.Card

/- Maya lists all the positive divisors of 2010. She then randomly selects two distinct divisors from this list. Let p be the probability that exactly one of the selected divisors is a perfect square. The probability p can be expressed in the form m/n, where m and n are relatively prime positive integers. Find m+n.-/

theorem AIME_Number_Theory_739 (m n : ℕ) (hn : n = (Nat.divisors (2010^2)).card.choose 2)
    (hm : m = Nat.card {⟨a,b⟩ : (Nat.divisors (2010^2)) × (Nat.divisors (2010^2)) |
      (IsSquare a.1 ∧ ¬IsSquare b.1)}) : (m + n)/(m.gcd n) = 107 := by

  -- First we compute the number of divisors of 2010
  have divisors_2010 : Nat.card (Nat.divisors (2010)) = 16 := by
    rw [Nat.card_eq_finsetCard, Nat.card_divisors]
    have : 2010 = 2*3*5*67 := by norm_num
    rw [this]
    repeat rw [Nat.factorization_mul, Nat.primeFactors_mul]
    · norm_num
      repeat rw [Finset.prod_union]
      all_goals simp
    all_goals linarith

  -- Then we compute the number of divisors of 2010^2
  have divisors_2010_2 : Nat.card (Nat.divisors (2010^2)) = 81 := by
    rw [Nat.card_eq_finsetCard, Nat.card_divisors]
    have : 2010 = 2*3*5*67 := by norm_num
    rw [Nat.factorization_pow, Nat.primeFactors_pow, this]
    repeat rw [Nat.factorization_mul, Nat.primeFactors_mul]
    · norm_num
      repeat rw [Finset.prod_union]
      all_goals simp
    all_goals linarith

  -- The number of pairs of divisors is the product of the number of divisors
  have set_prod (n : ℕ) : {⟨a,b⟩ : (Nat.divisors (n^2)) × (Nat.divisors (n^2)) |
      (IsSquare a.1 ∧ ¬IsSquare b.1)} ≃ {a : Nat.divisors (n^2) | IsSquare a.1} × {b : Nat.divisors (n^2) | ¬IsSquare b.1} := by
    use (fun ⟨x, hx⟩ ↦ ⟨⟨x.1, hx.1⟩, ⟨x.2, hx.2⟩⟩)
    · use (fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ⟨⟨x, y⟩, ⟨hx, hy⟩⟩)
    · intro ⟨x, hx⟩
      simp
    · intro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      simp

  -- The square root of a square is itself
  have sqrt_eq (n : ℕ) (hn : IsSquare n) : (Nat.sqrt n)^2 = n := by
    rw [Nat.find_spec hn, Nat.sqrt_eq, pow_two, ← Nat.find_spec hn]

  -- Divisors of n^2 that are squares are the squares of the divisors of n
  have square_divisors : {a : Nat.divisors (2010^2) | IsSquare a.1} ≃ Nat.divisors 2010 := by
    apply Equiv.ofBijective ?_ ?_
    · intro ⟨x, hx⟩
      use Nat.sqrt x
      rw [Nat.mem_divisors]
      constructor
      · rw [← Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)]
        apply Nat.dvd_of_mem_divisors
        · rw [sqrt_eq _ hx]
          exact x.2
      · linarith
    · rw [Function.bijective_iff_existsUnique]
      intro r
      use ⟨⟨(r.1)^2, ?_⟩, ?_⟩
      · simp only [Nat.reducePow, Set.coe_setOf, Set.mem_setOf_eq, Subtype.forall,
        Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        constructor
        · simp_rw [Nat.sqrt_eq']
        · intro n n_dvd n_square hn
          simp_rw [← hn, sqrt_eq _ n_square]
      · rw [Nat.mem_divisors]
        constructor
        · rw [Nat.pow_dvd_pow_iff]
          apply Nat.dvd_of_mem_divisors
          · exact r.2
          · linarith
        · linarith
      · simp only [Nat.reducePow, Set.mem_setOf_eq]
        use r.1
        linarith

  -- The sum of the cardinalities is the cardinality of all divisors
  have : Nat.card {b : Nat.divisors (2010^2) | ¬IsSquare b.1} = Nat.card (Nat.divisors (2010^2)) - Nat.card {a : Nat.divisors (2010^2) | IsSquare a.1} := by
    simp only [Set.coe_setOf, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Nat.mem_divisors, Fintype.card_coe]
    rw [ ← Nat.card_eq_finsetCard]
    simp

  -- We substitute the values and complete the computation
  rw [Nat.card_congr (set_prod 2010), Nat.card_prod, this, divisors_2010_2] at hm
  repeat rw [Nat.card_congr square_divisors, divisors_2010] at hm
  simp only [Nat.reduceSub, Nat.reduceMul] at hm
  rw [← Nat.card_eq_finsetCard, divisors_2010_2, Nat.choose_two_right] at hn
  simp only [Nat.add_one_sub_one, Nat.reduceMul, Nat.reduceDiv] at hn
  rw [hm, hn]
  norm_num