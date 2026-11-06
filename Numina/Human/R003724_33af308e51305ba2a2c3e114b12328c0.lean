import Mathlib

/- Show that, with two exceptions, every positive integer $q$ has an integer $p$ such that $\sqrt{56}< p / q<\sqrt{58}$.

http://nrich.maths.org -/



-- The tasks involves inequalities between square roots and rational numbers.

-- It is much easier to manipulate numbers when everything is an integer or a natural number.

-- So, we prove that to compare $\sqrt{n}$ with  $p / q$ is equivalent to comparing $q^2 n$ with $p^2$:


-- $\sqrt{n} = p / q$ implies $q^2 n = p^2$.
lemma sqrt_eq_int_div_int {n:ℕ} {p q: ℤ} (hq: 0 < q) (h: √(n:ℝ) = p/(q:ℝ) ): q^2 *n = p^2 := by {
  rify
  rw[←Real.sq_sqrt n.cast_nonneg', h]
  field_simp
}

-- $\sqrt{n} < p / q$ implies $q^2 n < p^2$.
lemma sqrt_lt_int_div_int {n:ℕ} {p q: ℤ} (hq: 0 < q) (hp: 0 < p) (h: √(n:ℝ) < p/(q:ℝ)): q^2 *n < p^2 := by {
  have hq2 : (q:ℝ)^2 ≠ 0 := by {
    simp
    linarith
  }
  have hqpos: 0 < (q:ℝ)^2 := lt_of_le_of_ne (sq_nonneg (q:ℝ)) hq2.symm
  rify at hp hq ⊢
  rw[<- mul_one ((p:ℝ)^2), <-div_self hq2, mul_div, mul_comm ((p:ℝ)^2), ← mul_div,
     mul_lt_mul_left hqpos, <-div_pow, ←Real.sq_sqrt n.cast_nonneg', sq_lt_sq]
  convert h using 1
  simp only [abs_eq_self, Real.sqrt_nonneg]
  rw[abs_eq_self]
  apply le_of_lt (div_pos hp hq)
}

-- $\sqrt{n} > p / q$ implies $q^2 n > p^2$.
lemma int_div_int_lt_sqrt {n:ℕ} {p q: ℤ} (hq: 0 < q) (hp: 0 < p) (h: p/(q:ℝ) < √(n:ℝ)):
    p^2 < q^2 *n := by {
  have hq2 : (q:ℝ)^2 ≠ 0 := by {
    simp
    linarith
  }
  have hqpos: 0 < (q:ℝ)^2 := lt_of_le_of_ne (sq_nonneg (q:ℝ)) hq2.symm

  rify at hp hq ⊢
  rw[<- mul_one ((p:ℝ)^2), <-div_self hq2, mul_div, mul_comm ((p:ℝ)^2), ← mul_div,
     mul_lt_mul_left hqpos, <-div_pow, ←Real.sq_sqrt n.cast_nonneg', sq_lt_sq]
  convert h using 1
  rw[abs_eq_self]
  apply le_of_lt (div_pos hp hq)
  simp only [abs_eq_self, Real.sqrt_nonneg]
}

-- The inverse implications are easy becasue they follow from case-by-case analysis of forward implications:

-- $\sqrt{n} = p / q$ if and only if $q^2 n = p^2$.
lemma sqrt_eq_int_div_int_iff {n:ℕ} {p q:ℤ} (hq: 0 < q) (hp: 0 < p): q^2 *n = p^2 ↔ √(n:ℝ) = p/(q:ℝ) := by {
  apply Iff.intro; {
    intro h
    by_contra hpq
    rw[<-ne_eq, ne_iff_lt_or_gt] at hpq
    cases hpq with
    |inl hpq => {
      apply sqrt_lt_int_div_int hq hp at hpq
      linarith
    }
    |inr hpq => {
      apply int_div_int_lt_sqrt hq hp at hpq
      linarith
    }
  }; {
    intro h
    apply sqrt_eq_int_div_int hq h
  }
}

-- $\sqrt{n} < p / q$ if and only if $q^2 n < p^2$.

lemma sqrt_lt_int_div_int_iff {n:ℕ} {p q:ℤ} (hq: 0 < q) (hp: 0 < p): q^2 *n < p^2 ↔ √(n:ℝ) < p/(q:ℝ) := by {
  apply Iff.intro; {
    intro h
    by_contra hpq
    rw[not_lt, le_iff_lt_or_eq] at hpq
    cases hpq with
    |inl hpq => {
      apply int_div_int_lt_sqrt hq hp at hpq
      linarith
    }
    |inr hpq => {
      have hqp := hpq.symm
      apply sqrt_eq_int_div_int hq at hqp
      linarith
    }
  }; {
    intro h
    exact sqrt_lt_int_div_int hq hp h
  }
}

-- $\sqrt{n} > p / q$ if and only if $q^2 n > p^2$.

lemma int_div_int_lt_sqrt_iff {n:ℕ} {p q:ℤ} (hq: 0 < q) (hp: 0 < p): p^2 < q^2 *n  ↔ p/(q:ℝ) < √(n:ℝ) := by {
  apply Iff.intro; {
    intro h
    by_contra hpq
    rw[not_lt, le_iff_lt_or_eq] at hpq
    cases hpq with
    |inl hpq => {
      apply sqrt_lt_int_div_int hq hp at hpq
      linarith
    }
    |inr hpq => {
      apply sqrt_eq_int_div_int hq at hpq
      linarith
    }
  }; {
    intro h
    exact int_div_int_lt_sqrt hq hp h
  }
}

--We also need the versions of those theorems for natural denominators.

lemma sqrt_eq_int_div_nat_iff {n q: ℕ} {p:ℤ} (hq: 0 < q) (hp: 0 < p): q^2 *n = p^2 ↔ √(n:ℝ) = p/(q:ℝ) := by {
  zify at *
  exact sqrt_eq_int_div_int_iff hq hp
}

lemma sqrt_lt_int_div_nat_iff {n q: ℕ} {p:ℤ}(hq: 0 < q) (hp: 0 < p): q^2 *n < p^2 ↔ √(n:ℝ) < p/(q:ℝ) := by {
  zify at *
  exact sqrt_lt_int_div_int_iff hq hp
}

lemma int_div_nat_lt_sqrt_iff {n q: ℕ} {p:ℤ} (hq: 0 < q) (hp: 0 < p): p^2 < q^2 *n  ↔ p/(q:ℝ) < √(n:ℝ) := by {
  zify at *
  exact int_div_int_lt_sqrt_iff hq hp
}

-- We need to show that a natural number of certain type exists between two given real numbers.

-- The foundational result of this type which we use is that the exists an integer number between any two numbers which are at greater than unit length from each other. 
lemma ex_int_of_add_one_lt {a b : ℝ} (hab: a + 1 < b) :
  ∃ r: ℤ, a < r ∧ r < b := by {
  by_cases h: ∃ r: ℤ, (r:ℝ) = b; {
    cases h with | intro r hr =>
    use r - 1
    apply And.intro; {
      simp
      rw[hr]
      linarith
    }; {
      simp
      rw[hr]
      linarith
    }
  }; {
    use Int.floor b
    apply And.intro; {
      apply lt_of_lt_of_le; {
        rw[<-add_lt_add_iff_right]
        apply Int.lt_floor_add_one
      }; {
        rw[Int.cast_le]
        apply Int.floor_le_floor (le_of_lt hab)
      }
    }; {
      apply lt_of_le_of_ne (Int.floor_le b)
      intro hb
      apply h
      use Int.floor b
    }
  }
}

-- When q is at least 8, the distance between $sqrt(56) q$ and $sqrt(8) q$ is greater than 1, so we can always fit a $p$ in between.
lemma case_eight_le {q: ℕ} (hq8: 8 ≤ q): ∃ p : ℤ, Real.sqrt 56 < p / (q:ℝ) ∧ p / (q:ℝ) < Real.sqrt 58 := by {

  have h: ∃ r: ℤ, Real.sqrt 56 * q < r ∧ r < Real.sqrt 58 * q := by {
    apply ex_int_of_add_one_lt
    rw[add_comm, <-add_lt_add_iff_right (-Real.sqrt 56 * q), add_assoc, <-add_mul, <-add_mul]
    simp
    have h7: 1 < (√58 + -√56)*(8:ℕ):= by {
      have h0: 0 < √58 + √56 := by {
        apply Right.add_pos;
        simp; simp
      }
      rw[<-mul_lt_mul_left h0, mul_one, <-sub_eq_add_neg, <-mul_assoc, <-sq_sub_sq]
      norm_num
      have h58: √58 < 8:= by {
        rw[Real.sqrt_lt (Nat.ofNat_nonneg 58) (Nat.ofNat_nonneg 8)]
        norm_num
      }
      have h56: √56 < 8:= by {
        rw[Real.sqrt_lt (Nat.ofNat_nonneg 56) (Nat.ofNat_nonneg 8)]
        norm_num
      }
      have h: √58 + √56 < 8+8:= add_lt_add h58 h56
      convert h
      norm_num
    }
    apply lt_of_lt_of_le h7
    rw[mul_le_mul_left]
    rw[Nat.cast_le]
    exact hq8
    norm_num
  }
  cases h with | intro r hr =>
  use r
  cases hr with |intro h56 h58 =>
  have hq: q ≠ 0 := Nat.not_eq_zero_of_lt hq8
  apply And.intro; {
    rw[<-mul_lt_mul_right]
    convert h56
    field_simp
    rw[Nat.cast_pos]
    exact Nat.zero_lt_of_ne_zero hq
  }; {
    rw[<-mul_lt_mul_right]
    convert h58
    field_simp
    rw[Nat.cast_pos]
    exact Nat.zero_lt_of_ne_zero hq
  }
}

-- All numbers which are less than 8 can be checked case by case, showing that only 1 and 3 do not work.
lemma case_nat {q: ℕ} (hq0: q≠0) (hq1: q ≠ 1) (hq3: q ≠ 3):
    ∃ p : ℤ, Real.sqrt (56:ℕ) < p / (q:ℝ) ∧ p / (q:ℝ) < Real.sqrt (58:ℕ) := by {
  match q with
  | 0 => simp at hq0
  | 1 => simp at hq1
  | 2 => {
    use 15
    apply And.intro; {
      rw[<-sqrt_lt_int_div_nat_iff]
      norm_num; norm_num; norm_num
    }; {
      rw[<-int_div_nat_lt_sqrt_iff]
      norm_num; norm_num; norm_num
    }
  }
  | 3 => simp at hq3
  | 4 => {
    use 30
    apply And.intro; {
      rw[<-sqrt_lt_int_div_nat_iff]
      norm_num; norm_num; norm_num
    }; {
      rw[<-int_div_nat_lt_sqrt_iff]
      norm_num; norm_num; norm_num
    }
  }
  | 5 => {
    use 38
    apply And.intro; {
      rw[<-sqrt_lt_int_div_nat_iff]
      norm_num; norm_num; norm_num
    }; {
      rw[<-int_div_nat_lt_sqrt_iff]
      norm_num; norm_num; norm_num
    }
  }
  | 6 => {
    use 45
    apply And.intro; {
      rw[<-sqrt_lt_int_div_nat_iff]
      norm_num; norm_num; norm_num
    }; {
      rw[<-int_div_nat_lt_sqrt_iff]
      norm_num; norm_num; norm_num
    }
  }
  | 7 =>{
    use 53
    apply And.intro; {
      rw[<-sqrt_lt_int_div_nat_iff]
      norm_num; norm_num; norm_num
    }; {
      rw[<-int_div_nat_lt_sqrt_iff]
      norm_num; norm_num; norm_num
    }
  }
  |t+8 => {
    exact case_eight_le (Nat.le_add_left 8 t)
  }
}

theorem number_theory_210231 :
    ∃ q1: ℤ, ∃ q2: ℤ, 0 < q1 ∧ 0 < q2 ∧ q1 ≠ q2 ∧
    ∀ q:ℤ, 0 < q → ((q ≠ q1 ∧ q ≠ q2) ↔
    ∃ p : ℤ, Real.sqrt 56 < p / (q:ℝ) ∧ p / (q:ℝ) < Real.sqrt 58) := by {
  -- First, we state that the two exceptions are precisely 1 and 3.
  use 1
  use 3
  simp only [zero_lt_one, Nat.ofNat_pos, ne_eq, OfNat.one_ne_ofNat, not_false_eq_true, true_and]
  intro q hq
  apply Iff.intro; {
    -- In forward direction, we use the previously proved result for natural numbers to generalise it to integer numbers.
    intro h
    have h0: q.natAbs ≠ 0 := by {
      simp
      exact Int.ne_of_gt hq
    }

    have hn := case_nat h0
    have hqc: (q:ℝ) = (q.natAbs:ℝ) := congrArg Int.cast (Int.eq_natAbs_of_zero_le (le_of_lt hq))
    
    rw[hqc]
    cases h with | intro h1 h3 =>
    apply hn; {
      rw[ne_eq, Int.natAbs_eq_iff]
      simp only [Nat.cast_one, not_or]
      apply And.intro h1
      intro h
      rw[h] at hq
      norm_num at hq
    }; {
      rw[ne_eq, Int.natAbs_eq_iff]
      simp only [Nat.cast_ofNat, not_or]
      apply And.intro h3
      intro h
      rw[h] at hq
      norm_num at hq
    }

  }; {
    -- In backward directions, we directly show that 1 and 3 are exceptions.
    intro h
    rw[←not_or]
    intro h13
    cases h with | intro p hp =>
    cases hp with | intro h1 h2 =>
    have hp: 0 < p := by {
      rify
      rify at hq
      exact lt_trans (mul_pos (Real.sqrt_pos.mpr Nat.ofNat_pos') hq) ((lt_div_iff₀ hq).mp h1)
    }
    have h0: 0 < p/(q:ℝ) := lt_of_le_of_lt (Real.sqrt_nonneg 56) h1
    apply sqrt_lt_int_div_int hq hp at h1
    apply int_div_int_lt_sqrt hq hp at h2;
    cases h13 with
    | inl h13 => {
        rw[h13] at h1 h2
        simp at h1 h2
        have h7 : p ≤ 7 := by nlinarith
        interval_cases p <;> linarith
    }
    | inr h13 => {
        rw[h13] at h1 h2
        simp at h1 h2
        have h25 : p ≤ 25 := by nlinarith
        interval_cases p <;> linarith
    }
  }
}