import Mathlib

/- The [harmonic mean](https://artofproblemsolving.com/wiki/index.php/Harmonic_mean) of
two positive integers is the reciprocal of the [arithmetic mean](https://artofproblemsolving.com/wiki/index.php/Arithmetic_mean)
of their reciprocals. For how many ordered pairs of positive integers $(x,y)$
with $x < y$ is the harmonic mean of $x$ and $y$ equal to $6^{20}$? -/
theorem algebra_96696 : Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < p.2 ∧ ((2 * p.1 * p.2) : ℚ) / (p.1 + p.2) = 6 ^ 20} = 799 := by
  -- rewrite the expression (2 * a * b) / (a + b) = 6 ^ 20 (over ℚ) to a * b = (3 ^ 30 * 2 ^ 19) * (a + b) (over ℕ)
  have h1 (a b : ℕ) (ha : a > 0) : ((2 * a * b) : ℚ) / (a + b) = 6 ^ 20 ↔ a * b = (3 ^ 20 * 2 ^ 19) * (a + b) := by
    rw [div_eq_iff (by norm_cast; omega)]
    norm_cast
    ring_nf
    omega
  -- if a * b = c * (a + b) (over ℕ) then (a - c) * (b - c) = c * c (over ℤ)
  have h2 (a b c : ℕ) : a * b = c * (a + b) ↔ ((a : ℤ) - c) * (b - c) = c * c := by
    ring_nf
    simp
    rw [show -((a : ℤ) * c) + (a * b - c * b) = a * b - (a * c + b * c) by ring]
    rw [Int.sub_eq_zero]
    norm_cast
  -- prove that (a - c) * (b - c) = c * c for positive integers implies that a > c and b > c
  -- we will use this property to go from ℤ to ℕ
  have h3 {a b c : ℕ} (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a < b) :
      ((a : ℤ) - c) * (b - c) = c * c → a > c ∧ b > c := by
    intro heq
    suffices a > c by omega
    -- consider two cases: c < a and c ≥ a
    rcases Nat.lt_or_ge c a with hac | hac
    · assumption
    -- consider two cases: c < b and c ≥ b
    rcases Nat.lt_or_ge c b with hbc | hbc
    · contrapose! heq
      apply ne_of_lt
      apply lt_of_le_of_lt _ (show 0 < (c : ℤ) * c by apply mul_pos <;> norm_cast)
      apply Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega)
    contrapose! heq
    apply ne_of_lt
    rw [show ((a : ℤ) - c) * (b - c) = (c - a) * (c - b) by ring]
    norm_cast
    gcongr <;> omega
  -- fix c = 3 ^ 20 * 2 ^ 19
  set c := 3 ^ 20 * 2 ^ 19 with c_eq
  have hc : c > 0 := by norm_num
  -- prove that the set from the theorem statement is equal to the set of ordered pairs of divisors (a < b) of c * c
  have hset_eq : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 < p.2 ∧ ((2 * p.1 * p.2) : ℚ) / (p.1 + p.2) = 6 ^ 20}.ncard =
              {q : ℕ × ℕ | q.1 > 0 ∧ q.2 > 0 ∧ q.1 < q.2 ∧ q.1 * q.2 = c * c}.ncard := by
    apply Set.ncard_congr (fun ⟨a, b⟩ _ => ⟨a - c, b - c⟩)
    · intro ⟨a, b⟩; simp
      intro ha hb hab
      rw [h1 _ _ ha, h2]
      intro heq
      have := h3 ha hb hc hab heq
      zify [this, heq]; simpa
    · intro ⟨a, b⟩ ⟨x, y⟩; simp
      intro ha hb hab
      rw [h1 _ _ ha, h2]
      intro eq1 hx hy hxy
      rw [h1 _ _ hx, h2]
      intro eq2
      have hxyc := h3 hx hy hc hxy eq2
      have habc := h3 ha hb hc hab eq1
      zify [hxyc, habc]
      omega
    · intro ⟨x, y⟩; simp
      intro hx hy hxy heq
      use x + c, Nat.add_sub_cancel_right _ _
      use y + c
      constructorm* _ ∧ _ <;> try omega
      rw [h1 _ _ (by omega), h2]
      simp only [Nat.cast_add, add_sub_cancel_right]
      norm_cast
  rw [hset_eq]; clear hset_eq h1 h2 h3
  set s1 := {q | _}
  set s2 := {q : ℕ × ℕ | q.1 > 0 ∧ q.2 > 0 ∧ q.1 > q.2 ∧ q.1 * q.2 = c * c}
  -- show that the set of all pairs of divisors of (c * c) is the union of sets of
  -- s1 (ordered pairs of divisors with a < b), s2 (ordered pairs of divisors with a > b),
  -- and a singleton set {⟨c, c⟩}
  have hset_eq : s1 ∪ s2 ∪ {⟨c, c⟩} = (c * c).divisorsAntidiagonal := by
    ext ⟨a, b⟩
    simp [s1, s2]
    constructor
    · intro h
      rcases h with h | h | h <;> try tauto
      rw [h.1, h.2]
    · intro heq
      have ha : 0 < a := by cases a <;> omega
      have hb : 0 < b := by cases b <;> omega
      rcases Nat.lt_trichotomy a b with h | h | h <;> try tauto
      left
      rw [h, ← pow_two, ← pow_two, sq_eq_sq₀ (by omega) (by omega)] at heq
      simp [h, heq]
  -- the cardinality of s1 is equal to the cardinality of s2
  have hs1_s2 : s1.ncard = s2.ncard := by
    apply Set.ncard_congr (fun ⟨a, b⟩ _ => ⟨b, a⟩)
    · intro ⟨a, b⟩; simp [s1, s2, mul_comm]; tauto
    · intro ⟨a, b⟩ ⟨x, y⟩; simp [s1, s2, mul_comm]; tauto
    · intro ⟨a, b⟩; simp [s1, s2, mul_comm]; tauto
  -- s1 and s2 are disjoint
  have hs12 : Disjoint s1 s2 := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨a, b⟩; simp [s1, s2]; omega
  -- s1 ∪ s2 does not contain ⟨c, c⟩
  have hs123 : Disjoint (s1 ∪ s2) {⟨c, c⟩} := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ⟨a, b⟩; simp [s1, s2]; omega
  -- s1 is finite (as a subset of a finite set (c * c).divisorsAntidiagonal)
  have hs1 : Finite s1 := by
    apply Finite.Set.subset (c * c).divisorsAntidiagonal
    rw [← hset_eq, Set.union_assoc]
    exact Set.subset_union_left
  -- s2 is finite (as a subset of a finite set (c * c).divisorsAntidiagonal)
  have hs2 : Finite s2 := by
    apply Finite.Set.subset (c * c).divisorsAntidiagonal
    rw [← hset_eq, Set.union_right_comm]
    exact Set.subset_union_right
  -- use properties of s1, s2 established above to prove that the cardinality
  -- of all pairs of divisors of (c * c) is s1.ncard + s2.ncard + 1
  have hcard : (c * c).divisorsAntidiagonal.card = s1.ncard + s2.ncard + 1 := by
    rw [← Set.ncard_coe_Finset, ←hset_eq]
    rw [Set.ncard_union_eq hs123, Set.ncard_union_eq hs12, Set.ncard_singleton]
  -- the cardinality of divisor of (c * c) is equal to the cardinality
  -- of all pairs of divisors (this fact is missing in Mathlib but it can be easily proven)
  have hdiv_card : (c * c).divisorsAntidiagonal.card = (c * c).divisors.card := by
    have := @Nat.map_div_left_divisors (c * c)
    apply_fun Finset.card at this
    rw [Finset.card_map] at this
    rw [this]
  -- since s1.ncard = n2.ncard, it is enough to show that the cardinality of
  -- divisors of (c * c) is 2 * 799 + 1
  suffices (c * c).divisors.card = 2 * 799 + 1 by omega
  rw [show c * c = (2 ^ 38 * 3 ^ 40) by norm_num]
  have hp : Nat.Coprime (2 ^ 38) (3 ^ 40) := by
    apply Nat.Coprime.pow
    norm_num
  -- count all divisors of c * c = 2 ^ 38 * 3 ^ 40 using basic properties of
  -- the arithmetic function σ₀
  rw [Nat.Coprime.card_divisors_mul hp]
  rw [←ArithmeticFunction.sigma_zero_apply, ←ArithmeticFunction.sigma_zero_apply]
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num)]
  rw [ArithmeticFunction.sigma_zero_apply_prime_pow (by norm_num)]