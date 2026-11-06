import Mathlib

/- Find the least positive integer $m$ such that $m^2 - m + 11$ is a product of at least four not necessarily distinct primes. -/
theorem number_theory_34466 :
    IsLeast {m : ℤ | 0 < m ∧ ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ m^2 - m + 11 = p * q * r * s} 132 := by
  constructor
  -- witness
  · norm_num
    exists 11; norm_num
    exists 11; norm_num
    exists 13; norm_num
    exists 11
  -- optimality
  · intros x hx
    simp only [exists_and_left, Set.mem_setOf_eq] at hx
    by_contra h
    obtain ⟨hx, p1, h1, p2, h2, p3, h3, p4, h4, hp⟩ := hx
    have aa := h1.pos
    have bb := h2.pos
    have cc := h3.pos
    have dd := h4.pos
    -- prove it has 4 prime factors
    have ak : ((x^2 - x + 11).toNat).primeFactorsList.length = 4 := by
      rw [hp]
      have nene : ((↑p1 : ℤ) * ↑p2 * ↑p3 * ↑p4).toNat = p1 * p2 * p3 * p4 := by
        zify; simp only [Int.ofNat_toNat, sup_eq_left]
        norm_cast
        clear * - aa bb cc dd
        omega
      rw [nene, ←ArithmeticFunction.cardFactors_apply]
      -- use the multiplicative property
      repeat rw [ArithmeticFunction.cardFactors_mul (by clear * - aa bb cc dd; intro jj; simp only [mul_eq_zero] at jj; omega) (by clear * - aa bb cc dd; omega)]
      rw [ArithmeticFunction.cardFactors_mul (by clear * - aa bb cc dd; omega) (by clear * - aa bb cc dd; omega)]
      simp [h1, h2, h3, h4]
    clear aa bb cc dd hp h1 h2 h3 h4 p1 p2 p3 p4
    -- turn into Fin for ease of manipulation
    obtain ⟨w, ww⟩ : ∃ j : Fin 132, j.1 = x := ⟨⟨x.toNat, by {
      zify; simp only [Int.ofNat_toNat, sup_lt_iff, Nat.ofNat_pos, and_true]
      exact Int.lt_of_not_ge h
    }⟩, by {
      zify; simp only [Int.ofNat_toNat, sup_eq_left]; linarith
    }⟩
    subst x
    revert w h hx ak
    -- optimality is now proven
    native_decide