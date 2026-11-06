import Mathlib

/- 20. Let $a, b, c$ be real numbers such that

$$

3 a b+2=6 b, \quad 3 b c+2=5 c, \quad 3 c a+2=4 a .

$$


Suppose the only possible values for the product $a b c$ are $r / s$ and $t / u$, where $r / s$ and $t / u$ are both fractions in lowest terms. Find $r+s+t+u$. -/
theorem algebra_225912 (p q : ℚ)
    (h : (fun (a, b, c) => a*b*c) '' {(a, b, c) : ℝ × ℝ × ℝ |
      3 * a * b + 2 = 6 * b
      ∧ 3 * b * c + 2 = 5 * c
      ∧ 3 * c * a + 2 = 4 * a} = {(p : ℝ), (q : ℝ)})
    : p.num + p.den + q.num + q.den = 18
  := by
    -- solutions to the three equations are a subset of solutions to 27abc^2 - 30abc + 8 = 0
    have set_subs : {(a, b, c) : ℝ × ℝ × ℝ  | 3 * a * b + 2 = 6 * b ∧ 3 * b * c + 2 = 5 * c ∧ 3 * c * a + 2 = 4 * a}
      ⊆ {(a, b, c) : ℝ × ℝ × ℝ| 27 * (a * b * c) ^ 2 - 30 * (a * b * c) + 8 = 0} := by
        intro ⟨a, b, c⟩
        simp only [Set.mem_setOf_eq, and_imp]
        intro aa bb cc
        -- a ≠ 0
        by_cases ha : a = 0
        · subst ha
          linarith

        -- b ≠ 0
        by_cases hb : b = 0
        · subst hb
          linarith

        -- c ≠ 0
        by_cases hc : c = 0
        · subst hc
          linarith

        -- divide the equations with b c and a, respectively
        have eq_1 : 3 * a + 2 / b = 6 := by
          field_simp
          exact aa
        have eq_2 : 3 * b + 2 / c = 5 := by
          field_simp
          exact bb
        have eq_3 : 3 * c + 2 / a = 4 := by
          field_simp
          exact cc

        -- multiply the equations together
        have mul : (3 * a + 2 / b) * (3 * b + 2 / c) * (3 * c + 2 / a) = 120 := by
          rw [eq_1, eq_2, eq_3]
          norm_num

        -- then expand LHS
        have lhs_eq : (3 * a + 2 / b) * (3 * b + 2 / c) * (3 * c + 2 / a) = 27 * a * b * c + 6 * (3 * a + 2 / b) + 6 * (3 * b + 2 / c) + 6 * (3 * c + 2 / a) + 8 / (a * b * c) := by
          ring_nf
          -- manually cancel variables
          have cancel_a : a * b * a⁻¹ = b := by field_simp
          have cancel_c : a * c * c⁻¹ = a := by field_simp
          have cancel_c' : b⁻¹ * c * c⁻¹ = b⁻¹ := by
            rw [mul_assoc]
            field_simp
          have cancel_a' : a * c⁻¹ * a⁻¹ = c⁻¹ := by
            rw [mul_comm, ←mul_assoc]
            field_simp
          have cancel_b : b * b⁻¹ * c = c := by field_simp
          have cancel_b' : b * b⁻¹ * a⁻¹ = a⁻¹ := by field_simp
          rw [cancel_a, cancel_c, cancel_a', cancel_b, cancel_c', cancel_b']
          ring_nf
        -- simplify using the equations
        rw [lhs_eq, eq_1, eq_2, eq_3] at mul
        field_simp at mul

        -- move terms to LHS
        rw [←sub_eq_zero] at mul
        -- then it's equal to the goal
        convert mul using 1
        ring

    have image_subs := Set.image_subset (fun (a, b, c) => a*b*c) set_subs
    rw [h] at image_subs

    -- replace abc = x
    have as_r : (fun (a, b, c) => a*b*c) '' {(a, b, c) : ℝ × ℝ × ℝ| 27 * (a * b * c) ^ 2 - 30 * (a * b * c) + 8 = 0 }
      = {x : ℝ| 27 * x ^ 2 - 30 * x + 8 = 0 } := by
        ext x
        simp only [Set.mem_image, Set.mem_setOf_eq, Prod.exists]
        constructor
        · intro ⟨a, b, c, h1, h2⟩
          rw [←h2]
          exact h1
        · intro aa
          refine ⟨x, 1, 1, ?_, ?_⟩
          · simpa only [mul_one] using aa
          · simp only [mul_one]

    -- then we have {p, q} ⊆ {x | 27 * x ^ 2 - 30 * x + 8 = 0}
    rw [as_r] at image_subs

    -- 4 / 9 and 2 / 3 are roots of the quadratic
    have quadratic_subs : {x : ℝ | 27 * x ^ 2 - 30 * x + 8 = 0} ⊆ {4 / 9, 2 / 3} := by
      intro x
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro h
      convert_to 27 * (x * x) + (-30) * x + 8 = 0 at h
      · ring

      -- discriminant is a square
      have eq_square := discrim_eq_sq_of_quadratic_eq_zero h

      -- if a = b ^ 2, then the square root of a is b or -b
      have eq_of : ∀ {a b : ℝ}, a = b ^ 2 → √a = b ∨ √a = -b := by
        intro a b h
        have a_nonneg : 0 ≤ a := by
          rw [h]
          positivity

        apply_fun Real.sqrt at h
        by_cases hb : 0 ≤ b
        · convert Or.inl h
          exact (Real.sqrt_sq hb).symm
        · convert Or.inr h using 2
          convert_to -b = √((-b) ^ 2)
          · simp only [even_two, Even.neg_pow]
          have neg_nonneg : 0 ≤ -b := by
            linarith
          exact (Real.sqrt_sq neg_nonneg).symm

      -- so we have two cases for the value of the discriminant
      have discrim_cases := eq_of eq_square

      -- we have two possible roots
      rw [pow_two] at eq_square
      have roots := (quadratic_eq_zero_iff (by norm_num) eq_square _).mp h

      -- 36 = 6 * 6
      have sq_36 : (36 : ℝ) = 6*6 := by norm_num

      -- case split on values of square root of disciminant to find roots
      cases' discrim_cases with h1 h2
      · rw [←h1, discrim] at roots
        norm_num at roots
        rw [sq_36] at roots
        simp only [Nat.ofNat_nonneg, Real.sqrt_mul_self] at roots
        norm_num at roots
        exact roots.symm
      · replace h2 : -√(discrim 27 (-30) 8) = (2 * 27 * x + -30) := by linarith
        rw [←h2, discrim] at roots
        norm_num at roots
        rw [sq_36] at roots
        simp only [Nat.ofNat_nonneg, Real.sqrt_mul_self] at roots
        norm_num at roots
        exact roots

    -- then we have that {p, q} ⊆ {4 / 9, 2 / 3}
    have subs := image_subs.trans quadratic_subs

    -- but we also have that {4 / 9, 2 / 3} ⊆ {p, q}
    have subs_2 : ({4 / 9, 2 / 3} : Set ℝ) ⊆ ({↑p, ↑q} : Set ℝ) := by
      -- we'll check that there are solutions to the three equations when the product is 4 / 9 or 2 / 3
      rw [←h]
      intro p
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Set.mem_setOf_eq,
        Prod.exists]
      intro aa
      rcases aa with h1 | h2
      -- when abc = 4 / 9, it works with a = 1, b = 2 / 3, c = 2 / 3
      · refine ⟨1, (2 / 3 : ℝ), (2 / 3 : ℝ), ?_, ?_⟩
        norm_num
        norm_num
        exact h1.symm
      -- when abc = 2 / 3, it works with a = 8 / 7, b = 7 / 9, c = 3 / 4
      · refine ⟨(8 / 7 : ℝ), (7 / 9 : ℝ), (3 / 4 : ℝ), ?_, ?_⟩
        norm_num
        norm_num
        exact h2.symm

    -- so we have {p, q} = {4 / 9, 2 / 3}
    have set_eq : ({↑p, ↑q} : Set ℝ) = ({4 / 9, 2 / 3} : Set ℝ) := subs.antisymm subs_2

    -- if two sets with two elements are equal, then there are two possible equalities
    have sets_eq : ∀ {a b c d : ℝ}, {a, b} = ({c, d} : Set ℝ) → c ≠ d → a = c ∧ b = d ∨ a = d ∧ b = c := by
      intro a b c d eq ne
      have ne2 : a ≠ b := by
        by_contra hh
        rw [hh] at eq
        simp only [Set.mem_singleton_iff, Set.insert_eq_of_mem] at eq
        have c_mem : c ∈ ({b} : Set ℝ) := by
          rw [eq]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]
        have d_mem : d ∈ ({b} : Set ℝ) := by
          rw [eq]
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

        simp only [Set.mem_singleton_iff] at c_mem d_mem
        rw [c_mem, d_mem] at ne
        contradiction

      have a_mem : a ∈ ({c, d} : Set ℝ) := by
        rw [←eq]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

      have b_mem : b ∈ ({c, d} : Set ℝ) := by
        rw [←eq]
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]

      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at a_mem b_mem

      cases' a_mem with h1 h2
      · cases' b_mem with h3 h4
        · rw [h1, h3] at ne2
          contradiction
        · tauto
      · cases' b_mem with h3 h4
        · tauto
        · rw [h2, h4] at ne2
          contradiction

    -- in our case, either p = 4 / 9 and q = 2 / 3, or p = 2 / 3 and q = 4 / 9
    have our_case := sets_eq set_eq (by norm_num)

    -- if rationals casted to real numbers are equal to something that looks rational,
    -- then they're actually equal to that rational number
    have cast_eq : ∀ {qq : ℚ}, (qq : ℝ) = 4 / 9 → qq = 4 / 9 := by
      intro q qh
      rify
      exact qh
    have cast_eq2 : ∀ {qq : ℚ}, (qq : ℝ) = 2 / 3 → qq = 2 / 3 := by
      intro q qh
      rify
      exact qh

    -- verify that for each case, the sum of parts is equal to 18
    rcases our_case with ⟨h1, h2⟩ | ⟨h3, h4⟩
    · replace h1 := cast_eq h1
      replace h2 := cast_eq2 h2
      rw [h1, h2]
      norm_num
    · replace h3 := cast_eq2 h3
      replace h4 := cast_eq h4
      rw [h3, h4]
      norm_num