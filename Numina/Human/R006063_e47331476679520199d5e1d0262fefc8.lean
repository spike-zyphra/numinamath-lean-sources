import Mathlib

/- # Problem:
 In how many ways can the cells of a $4 \times 4$ table be filled in with the digits $1,2, \ldots, 9$ so that each of the 4 -digit numbers formed by the columns is divisible by each of the 4-digit numbers formed by the rows?
9 If $a$ and $b$ are 4-digit numbers with the same first digit, and $a$ divides $b$, then since $b < a+1000 \leq 2 a, b$ must equal $a$. In particular, since the number formed by the first row of the table divides the number in the first column (and both have the same first digit), these numbers must be equal; call their common value $n$. Then, for $k=2,3$, or 4 , we find that the number in the $k$ th column and the number in the $k$ th row have the same first digit (namely the $k$ th digit of $n$ ), so by the same reasoning, they are equal. Also, the smallest number $b$ formed by any column is divisible by the largest number $a$ formed by any row, but by the symmetry just proven, $a$ is also the largest number formed by any column, so $a \geq b$. Since $b$ is divisible by $a$, we must have equality. Then all columns contain the same number - and hence all rows also contain the same number - which is only possible if all 16 cells contain the same digit. Conversely, for each $d=1, \ldots, 9$, filling in all 16 cells with the digit $d$ clearly gives a table meeting the required condition, so we have exactly 9 such tables, one for each digit. -/

lemma list_length_eq_four {l : List ℕ} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] :=
  ⟨fun _ => let [a, b, c, d] := l; ⟨a, b, c, d, rfl⟩, fun ⟨_, _, _, _, e⟩ => e ▸ rfl⟩


lemma four_digit_dvd_eq {a b : ℕ} (ha : a ∈ Finset.Icc 1000 9999) (hb : b ∈ Finset.Icc 1000 9999) (hab : a ∣ b) (hd: (Nat.digits 10 a)[3]! = (Nat.digits 10 b)[3]!): a = b := by
  obtain ⟨k, hk⟩ := hab
  have hk0 : k ≠ 0 := by
    by_contra h
    subst k b
    simp at hb

  by_contra hcontra
  have hk1 : k ≠ 1 := by
    by_contra h
    subst k
    omega

  have hk2 : 2 ≤ k := by omega


  have : (Nat.digits 10 a).length = 4 := by
    simp at ha
    have := @Nat.le_digits_len_le 10 1000 a (by omega)
    rw [show (Nat.digits 10 1000).length = 4 by simp] at this
    have := @Nat.le_digits_len_le 10 a 9999 (by omega)
    rw [show (Nat.digits 10 9999).length = 4 by simp] at this
    omega

  rw [list_length_eq_four] at this
  obtain ⟨a0, a1, a2, a3, ha_eq⟩ := this

  have h1 : 1000 * a3 ≤ a := by
    have := Nat.ofDigits_digits 10 a
    rw [ha_eq] at this
    rw [Nat.ofDigits_eq_foldr] at this
    simp at this
    omega

  have h2 : b < 1000 * (1 + a3) := by
    have : (Nat.digits 10 b).length = 4 := by
      simp at hb
      have := @Nat.le_digits_len_le 10 1000 b (by omega)
      rw [show (Nat.digits 10 1000).length = 4 by simp] at this
      have := @Nat.le_digits_len_le 10 b 9999 (by omega)
      rw [show (Nat.digits 10 9999).length = 4 by simp] at this
      omega

    rw [list_length_eq_four] at this
    obtain ⟨b0, b1, b2, b3, hb_eq⟩ := this

    have : a3 = b3 := by
      rw [ha_eq] at hd
      rw [hb_eq] at hd
      simp at hd
      exact hd

    subst a3
    have := Nat.ofDigits_digits 10 b
    rw [hb_eq] at this
    rw [Nat.ofDigits_eq_foldr] at this
    simp at this
    rw [← this]
    have : b0 < 10 := by
      apply @Nat.digits_lt_base 10 b b0
      . norm_num
      . rw [hb_eq]
        simp

    have : b1 < 10 := by
      apply @Nat.digits_lt_base 10 b b1
      . norm_num
      . rw [hb_eq]
        simp

    have : b2 < 10 := by
      apply @Nat.digits_lt_base 10 b b2
      . norm_num
      . rw [hb_eq]
        simp

    omega

  have : a3 = 0 := by nlinarith
  subst a3
  simp at h2 hb
  omega


theorem number_theory_611344 :
  Set.ncard {a : Fin 4 → Fin 4 → ℕ | (∀ i j, a i j ∈ Finset.Icc 1 9) ∧
    (∀ i j, Nat.ofDigits 10 [a i 3, a i 2, a i 1, a i 0] ∣ Nat.ofDigits 10 [a 3 j, a 2 j, a 1 j, a 0 j])} = 9 := by

  let f : ℕ → Fin 4 → Fin 4 → ℕ := fun n i j => n

  suffices {a : Fin 4 → Fin 4 → ℕ | (∀ i j, a i j ∈ Finset.Icc 1 9) ∧
    (∀ i j, Nat.ofDigits 10 [a i 3, a i 2, a i 1, a i 0] ∣ Nat.ofDigits 10 [a 3 j, a 2 j, a 1 j, a 0 j])} = f '' Finset.Icc 1 9 by

    rw [this]
    have : 9 = (Finset.Icc 1 9).toSet.ncard := by
      rw [show (Finset.Icc 1 9) = {1,2,3,4,5,6,7,8,9} by ext n; simp; omega]
      simp
      repeat rw [Set.ncard_insert_of_not_mem]
      all_goals simp

    nth_rw 2 [this]
    apply Set.ncard_image_of_injOn
    simp
    intro x1 hx1 x2 hx2 h
    unfold f at h
    simp at hx1 hx2
    obtain ⟨hx1_1, hx1_2⟩ := hx1
    obtain ⟨hx2_1, hx2_2⟩ := hx2
    interval_cases x1
    all_goals interval_cases x2
    all_goals try omega
    all_goals contrapose h; native_decide


  ext a
  simp
  constructor
  . intro ⟨h1, h2⟩
    use a 0 0
    refine ⟨h1 0 0, ?_⟩
    suffices ∀ i j, a i j = a 0 0 by
      ext i j
      unfold f
      have := this i j
      exact this.symm

    let row := fun i => Nat.ofDigits 10 [a i 3, a i 2, a i 1, a i 0]
    let col := fun j => Nat.ofDigits 10 [a 3 j, a 2 j, a 1 j, a 0 j]

    have row_range : ∀ i, row i ∈ Finset.Icc 1000 9999 := by
      intro i
      simp
      constructor
      . unfold row
        rw [Nat.ofDigits_eq_foldr]
        simp
        have : 1 ≤ a i 0 := (h1 i 0).1
        have : 1 ≤ a i 1 := (h1 i 1).1
        have : 1 ≤ a i 2 := (h1 i 2).1
        have : 1 ≤ a i 3 := (h1 i 3).1
        omega

      . have : ∀ x ∈ [a i 3, a i 2, a i 1, a i 0], x < 10 := by
          intro x hx
          simp at hx
          rcases hx with rfl | rfl | rfl | rfl
          . have := h1 i 3
            omega
          . have := h1 i 2
            omega
          . have := h1 i 1
            omega
          . have := h1 i 0
            omega
        have := @Nat.ofDigits_lt_base_pow_length 10 [a i 3, a i 2, a i 1, a i 0] (by norm_num) this
        simp at this
        unfold row
        omega

    have col_range : ∀ j, col j ∈ Finset.Icc 1000 9999 := by
      intro j
      simp
      constructor
      . unfold col
        rw [Nat.ofDigits_eq_foldr]
        simp
        have : 1 ≤ a 3 j := (h1 3 j).1
        have : 1 ≤ a 2 j := (h1 2 j).1
        have : 1 ≤ a 1 j := (h1 1 j).1
        have : 1 ≤ a 0 j := (h1 0 j).1
        omega
      . have : ∀ x ∈ [a 3 j, a 2 j, a 1 j, a 0 j], x < 10 := by
          intro x hx
          simp at hx
          rcases hx with rfl | rfl | rfl | rfl
          . have := h1 3 j
            omega
          . have := h1 2 j
            omega
          . have := h1 1 j
            omega
          . have := h1 0 j
            omega
        have := @Nat.ofDigits_lt_base_pow_length 10 [a 3 j, a 2 j, a 1 j, a 0 j] (by norm_num) this
        simp at this
        unfold col
        omega

    have row_eq : ∀ i, Nat.digits 10 (row i) = [a i 3, a i 2, a i 1, a i 0] := by
      intro i
      rw [Nat.digits_ofDigits]
      . norm_num
      . intro l hl
        simp at hl
        rcases hl with rfl | rfl | rfl | rfl
        . have := h1 i 3
          omega
        . have := h1 i 2
          omega
        . have := h1 i 1
          omega
        . have := h1 i 0
          omega
      . intro h
        simp
        have := h1 i 0
        omega

    have col_eq : ∀ j, Nat.digits 10 (col j) = [a 3 j, a 2 j, a 1 j, a 0 j] := by
      intro j
      rw [Nat.digits_ofDigits]
      . norm_num
      . intro l hl
        simp at hl
        rcases hl with rfl | rfl | rfl | rfl
        . have := h1 3 j
          omega
        . have := h1 2 j
          omega
        . have := h1 1 j
          omega
        . have := h1 0 j
          omega
      . intro h
        simp
        have := h1 0 j
        omega

    have heq0 : row 0 = col 0 := by
      apply four_digit_dvd_eq
      . exact row_range 0
      . exact col_range 0
      . exact h2 0 0
      . rw [row_eq 0, col_eq 0]
        simp

    have : a 3 0 = a 0 3 ∧ a 2 0 = a 0 2 ∧ a 1 0 = a 0 1 := by
      have := row_eq 0
      rw [heq0] at this
      rw [col_eq 0] at this
      simp at this
      exact this

    have heq1: row 1 = col 1 := by
      apply four_digit_dvd_eq
      . exact row_range 1
      . exact col_range 1
      . exact h2 1 1
      . rw [row_eq 1, col_eq 1]
        simp
        omega

    have : a 3 1 = a 1 3 ∧ a 2 1 = a 1 2 ∧ a 0 1 = a 1 0 := by
      have := row_eq 1
      rw [heq1] at this
      rw [col_eq 1] at this
      simp at this
      exact this

    have heq2 : row 2 = col 2 := by
      apply four_digit_dvd_eq
      . exact row_range 2
      . exact col_range 2
      . exact h2 2 2
      . rw [row_eq 2, col_eq 2]
        simp
        omega

    have : a 3 2 = a 2 3 ∧ a 1 2 = a 2 1 ∧ a 0 2 = a 2 0 := by
      have := row_eq 2
      rw [heq2] at this
      rw [col_eq 2] at this
      simp at this
      exact this

    have heq3 : row 3 = col 3 := by
      apply four_digit_dvd_eq
      . exact row_range 3
      . exact col_range 3
      . exact h2 3 3
      . rw [row_eq 3, col_eq 3]
        simp
        omega

    have : a 2 3 = a 3 2 ∧ a 1 3 = a 3 1 ∧ a 0 3 = a 3 0 := by
      have := row_eq 3
      rw [heq3] at this
      rw [col_eq 3] at this
      simp at this
      exact this

    have : 0 < col 0 := by
      have := col_range 0
      simp at this
      omega

    have : 0 < col 1 := by
      have := col_range 1
      simp at this
      omega

    have : 0 < col 2 := by
      have := col_range 2
      simp at this
      omega

    have : 0 < col 3 := by
      have := col_range 3
      simp at this
      omega

    have hc01: col 0 = col 1 := by
      have : row 0 ∣ col 1 := h2 0 1
      rw [heq0] at this
      apply Nat.le_of_dvd (by assumption) at this
      have : row 1 ∣ col 0 := h2 1 0
      rw [heq1] at this
      apply Nat.le_of_dvd (by assumption) at this
      omega

    have : a 3 1 = a 3 0 ∧ a 2 1 = a 2 0 ∧ a 1 1 = a 1 0 ∧ a 0 1 = a 0 0 := by
      have := col_eq 0
      rw [hc01] at this
      rw [col_eq 1] at this
      simp at this
      exact this

    have hc02 : col 0 = col 2 := by
      have : row 0 ∣ col 2 := h2 0 2
      rw [heq0] at this
      apply Nat.le_of_dvd (by assumption) at this
      have : row 2 ∣ col 0 := h2 2 0
      rw [heq2] at this
      apply Nat.le_of_dvd (by assumption) at this
      omega

    have : a 3 2 = a 3 0 ∧ a 2 2 = a 2 0 ∧ a 1 2 = a 1 0 ∧ a 0 2 = a 0 0 := by
      have := col_eq 0
      rw [hc02] at this
      rw [col_eq 2] at this
      simp at this
      exact this

    have hc03 : col 0 = col 3 := by
      have : row 0 ∣ col 3 := h2 0 3
      rw [heq0] at this
      apply Nat.le_of_dvd (by assumption) at this
      have : row 3 ∣ col 0 := h2 3 0
      rw [heq3] at this
      apply Nat.le_of_dvd (by assumption) at this
      omega

    have : a 3 3 = a 3 0 ∧ a 2 3 = a 2 0 ∧ a 1 3 = a 1 0 ∧ a 0 3 = a 0 0 := by
      have := col_eq 0
      rw [hc03] at this
      rw [col_eq 3] at this
      simp at this
      exact this

    intro i j
    fin_cases i <;> fin_cases j <;> simp <;> omega

  . rintro ⟨c, ⟨hc1, hc2⟩, hc3⟩
    constructor
    . intro i j
      rw [← hc3]
      unfold f
      omega
    . intro i j
      rw [← hc3]
