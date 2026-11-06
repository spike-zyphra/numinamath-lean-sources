import Mathlib

/- $8 \cdot 90$ Let the sequence of non-zero real numbers $x_{1}, x_{2}, x_{3}, \cdots$ satisfy

$$

x_{n}=\frac{x_{n-2} x_{n-1}}{2 x_{n-2}-x_{n-1}}, n=3,4,5, \cdots

$$


Find the necessary and sufficient condition that $x_{1}$ and $x_{2}$ must satisfy so that the sequence has infinitely many integer terms. -/

-- using induction, prove fomula relating x (n + k) and x n, x (n + 1)
lemma l_index_add {x : ℕ → ℝ} (hx : ∀ n, x n ≠ 0) (h₀ : ∀ n, 2 * x n - x (n + 1) ≠ 0)
    (h : ∀ n, x (n + 2) = (x n * x (n + 1)) / (2 * x n - x (n + 1))) (k: ℕ) (hk : 2 ≤ k) :
    ∀ n, x (n + k) = x n * x (n + 1) / (k * x n - (k - 1) * x (n + 1)) := by
  induction' k, hk using Nat.le_induction with m hm hm'
  . rintro n
    rw [h]
    norm_num
  . rintro n
    rw [show n + (m + 1) = (n + 1) + m by ring]
    rw [hm']
    push_cast
    repeat conv in n + 1 + 1 => ring_nf; rw [add_comm]
    conv_rhs => arg 2; arg 2; arg 1; ring_nf
    rw [h]
    have := h₀ n
    have := hx (n + 1)
    field_simp
    conv_lhs =>
      arg 2; equals x (n + 1) * ((m + 1) * x n - m * x (n + 1)) => ring
    rw [mul_div_mul_left _ _  (by assumption)]

-- if b ≠ 0 then a / (m * b + c) will eventually get inside (-1, 1)
lemma l_exists_constant_to_bound (a b c : ℝ) (ha : b ≠ 0) : ∃ (n : ℕ), ∀ m > n, a / (m * b + c) ∈ Set.Ioo (-1) 1 := by
  simp
  -- conver to absolute value
  simp_rw [← abs_lt, abs_div]
  -- to prove this we prove as |a| + 1 = o(x * b + c) as then eventually |a| + 1 ≤ |x * b + c| so the ratio is less than 1
  suffices (fun x => |a| + 1) =o[Filter.atTop] (fun x => x * b + c) by
    have := Asymptotics.IsLittleO.eventuallyLE this
    simp at this
    obtain ⟨n', hn'⟩ := this
    use Nat.ceil n'
    rintro m hm
    specialize hn' m
    have :  n' ≤ ↑m := by
      apply le_of_lt
      calc
        _ ≤ (⌈n'⌉₊ : ℝ) := Nat.le_ceil n'
        _ < m := by norm_cast
    specialize hn' this
    rw [abs_of_nonneg (by positivity)] at hn'
    rw [div_lt_one_iff]
    left
    and_intros
    . linarith [show 0 ≤ |a| by positivity]
    . linarith
  -- to prove the little oh, we'll prove (|a| + 1) / (x * b + c) tends to 0
  refine Asymptotics.isLittleO_iff_tendsto' ?_ |>.mpr ?_
  -- this requires proving that eventually both terms of ratio are 0 simultaneously by showing x > |-c|/|b| + 1, x * b + c is never 0, we prove this
  . simp [show |a| + 1 ≠ 0 by positivity]
    use |-c|/|b| + 1
    rintro x hx
    have : (|-c| / |b| + 1) * |b| ≤ x * |b| := by gcongr
    ring_nf at this
    have hb : |b| ≠ 0 := by simpa
    conv_lhs at this => arg 1; equals |-c| => field_simp
    by_contra
    have h'' : |x * b| = |-c| := by congr; linarith
    have : 0 ≤ |-c|/|b| := by positivity
    rw [abs_mul, abs_of_nonneg (by linarith )] at h''
    have : 0 < |b| := by positivity
    linarith
  -- to prove ratio tens to 0, wlog 0 < b as otherwise by using a, -b, -c we can prove negative of raio tends to 0
  . wlog hb : 0 < b generalizing a b c
    . simp at hb
      replace hb : b < 0 := by apply lt_of_le_of_ne hb ha
      specialize this a (-b) (-c) (by linarith) (by linarith)
      convert this.neg using 1
      . ext x
        ring_nf
        rw [← mul_neg, neg_inv]
        ring_nf
        congr
        rw [neg_inv]
        ring_nf
      . simp
    -- denomniator tends to infinity as b * x + c is a linear function with 0 < b
    apply Filter.Tendsto.const_div_atTop
    simp_rw [add_comm]
    apply Filter.tendsto_atTop_add_const_left
    simp_rw [mul_comm]
    apply Filter.Tendsto.const_mul_atTop hb
    apply Filter.tendsto_id

theorem algebra_100587 (x : ℕ → ℝ) (hx : ∀ n, x n ≠ 0)
    (h₀ : ∀ n, 2 * x n - x (n + 1) ≠ 0) (h : ∀ n, x (n + 2) = (x n * x (n + 1)) / (2 * x n - x (n + 1))) :
    {n | ∃ m : ℤ, x n = m}.Infinite ↔ x 0 = x 1 ∧ ∃ m : ℤ, x 0 = m := by
  -- prove general term using first lemma using just x 0, x 1
  have h_general_term (n : ℕ) : x (n + 2) = x 0 * x 1 / ((n + 3) * (x 0 - x 1) + 2 * x 1 - x 0) := by
    have := l_index_add hx h₀ h (n + 2) (by linarith) 0
    ring_nf at this ⊢
    rw [this]
    congr 2
    push_cast
    ring
  rw [Set.infinite_iff_exists_gt]
  constructor
  . rintro h'
    -- x 0 = x 1 as otherwise by second lemma we have in general formula, the expression is 0 as the only possible integer, but then  contradiciton
    have h01 : x 0 = x 1 := by
      by_contra h01
      change x 0 ≠ x 1 at h01
      rw [← sub_ne_zero] at h01
      simp_rw [← add_sub] at h_general_term
      obtain ⟨n, hn⟩ := l_exists_constant_to_bound (x 0 * x 1) (x 0 - x 1) (2 * x 1 - x 0) h01
      obtain ⟨k, ⟨m, hm⟩ , hk⟩ := h' (n + 5)
      specialize h_general_term (k - 2)
      conv_rhs at h_general_term => arg 2; arg 1; arg 1; equals ↑k + 1 => norm_cast; omega
      specialize hn (k + 1) (by linarith)
      push_cast at hn
      rw [← h_general_term] at hn
      conv at hn => arg 2; arg 1; equals k => omega
      rw [hm] at hn
      simp at hn
      convert_to -1 < m ∧ m < 1 at hn <;> norm_cast
      have : m = 0 := by omega
      rw [this] at hm
      simp at hm
      specialize hx k
      contradiction
    -- using x 0 = x 1, we get all terms are x0, so obivoiusly x 0 is an integer
    simp [← h01]
    rw [← h01] at h_general_term
    simp at h_general_term
    ring_nf at h_general_term
    specialize hx 0
    conv at h_general_term in  x 0 ^ 2 * (x 0)⁻¹ =>
      equals x 0 => field_simp; ring
    obtain ⟨n, hn , hn'⟩ := h' 2
    specialize h_general_term (n - 2)
    conv_lhs at h_general_term => arg 1; equals n => omega
    rw [← h_general_term]
    exact hn
  -- if x 0 = x 1 is an intger, then simplifying formula we get x n = x 0, always so for any N, there is N + 2 > n which is x 0 and an integer, so set is infinite
  . rintro ⟨h01, h0⟩
    simp_rw [← h01] at h_general_term
    simp at h_general_term
    ring_nf at h_general_term
    specialize hx 0
    conv at h_general_term in  x 0 ^ 2 * (x 0)⁻¹ =>
      equals x 0 => field_simp; ring
    obtain ⟨m, hm⟩ := h0
    rintro n
    use n + 2
    and_intros
    . use m
      rwa [add_comm, h_general_term]
    . linarith