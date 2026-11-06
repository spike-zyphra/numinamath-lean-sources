import Mathlib

def nth
  | 0 => 1
  | m + 1 => m + nth m

def nth_series (n:ℕ) := Finset.Ico (nth n) (nth (n+1))

def closed_form_nth (n : ℕ) :=
  (n * (n - 1)) / 2 + 1

def closed_form_series (n : ℕ) :=
  Finset.Icc (closed_form_nth n) (closed_form_nth (n+1) - 1)

def closed_form_sum (n : ℕ) :=
  (n + 1) * closed_form_nth n - 1

lemma even_gauss : ∀ n, Even (n * (n - 1)) := by
  intro n
  rw [@Nat.even_mul]
  simp [@Nat.even_iff]
  omega

lemma even_gauss' : ∀ n, Even ((n + 1) * n) := by
  intro n
  rw [@Nat.even_mul]
  simp [@Nat.even_iff]
  omega

lemma closed_form_nth_eq : nth = closed_form_nth := by
  ext n
  induction' n with k ih
  · rfl
  · unfold nth
    rw [ih]
    suffices 2 * k + closed_form_nth k * 2 = closed_form_nth k.succ * 2 by
      linarith

    unfold closed_form_nth

    have : Even (k * (k - 1)) := @even_gauss k
    have hk := @Nat.div_two_mul_two_of_even (k * (k - 1)) (by assumption)

    have : Even ((k * k) + k) := by
      have := @even_gauss' k
      convert this using 1
      linarith
    have hk2 := @Nat.div_two_mul_two_of_even ((k * k) + k) (by assumption)

    field_simp [add_mul, hk, hk2]
    abel_nf
    simp [two_mul, Nat.mul_sub]
    conv_rhs => rw [add_comm]
    suffices k + (k * k - k) = k * k by
      linarith
    rw [Nat.add_comm]
    have : k ≤ k * k := by
      by_cases k = 0
      · subst k; rfl
      · conv_lhs => rw [<- mul_one k]
        gcongr
        suffices 0 < k from this
        positivity

    field_simp


lemma closed_form_eq : ∀ n, (nth_series n).sum id = closed_form_sum n := by
  intro n
  induction' n with k ih
  · unfold closed_form_sum; norm_num; rfl
  · unfold nth_series at *
    simp_all
    replace range_eq := Finset.sum_Ico_eq_sum_range id (nth k) (nth (k+1))
    simp at range_eq
    rw [range_eq] at ih
    replace range_eq := Finset.sum_Ico_eq_sum_range id (nth (k + 1)) (nth (k+1 + 1))
    simp at range_eq
    rw [range_eq]
    clear range_eq
    unfold closed_form_sum at *
    rw [<- closed_form_nth_eq] at *
    simp [nth] at *
    simp [@Finset.sum_range_add]
    have pos_nth : 0 < nth (k + 1) := by
      by_cases h : k = 0
      · subst k
        simp [nth]
      · simp [nth]
        apply Or.inl
        positivity

    suffices ∑ x ∈ Finset.range k, (k + nth k + x) + (k + nth k + k) + 1 = (k + 1 + 1) * (k + nth k) by
      omega

    rw [show ∑ x ∈ Finset.range k, (k + nth k + x) = ∑ x ∈ Finset.range k, (k + nth k + ·) x by rfl]
    suffices 1 + ∑ x ∈ Finset.range k, (k + nth k + x) =  k * nth k + k ^ 2 + nth k by
      linarith

    rw [@Finset.sum_add_distrib] at *
    simp [Finset.sum_const]

    suffices 1 + ∑ x ∈ Finset.range k, x = nth k by
      linarith

    rw [Finset.sum_range_id]
    rw [closed_form_nth_eq, closed_form_nth, add_comm]


theorem number_theory_251213 : (nth_series 21).sum id = 4641 := by
  rw [closed_form_eq]
  rfl
