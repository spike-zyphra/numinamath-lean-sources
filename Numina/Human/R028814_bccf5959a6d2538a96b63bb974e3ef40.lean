
import Mathlib

open scoped BigOperators


/- Define the function $f:(0,1) \rightarrow(0,1)$ by  $$ f(x)= \begin{cases}x+\frac{1}{2} & \text { if } x<\frac{1}{2} \\ x^{2} & \text { if } x \geqslant \frac{1}{2}\end{cases} $$  Let $a$ and $b$ be two real numbers such that $0<a<b<1$.
We define the sequences $a_{n}$ and $b_{n}$ by $a_{0}=a, b_{0}=b$, and $a_{n}=f\left(a_{n-1}\right), b_{n}=f\left(b_{n-1}\right)$ for $n>0$.
Show that there exists a positive integer $n$ such that  $$ \left(a_{n}-a_{n-1}\right)\left(b_{n}-b_{n-1}\right)<0 .
$$  (Denmark) -/
theorem algebra_24389
    {f : ℝ → ℝ}
    (hf : ∀ x, x < 1 / 2 → f x = x + 1 / 2)
    (hf' : ∀ x, x ≥ 1 / 2 → f x = x ^ 2)
    (a b : ℝ)
    (a_seq b_seq : ℕ → ℝ)
    (h_a0 : a_seq 0 = a)
    (h_b0 : b_seq 0 = b)
    (ha : ∀ n : ℕ, a_seq (n + 1) = f (a_seq n))
    (hb : ∀ n : ℕ, b_seq (n + 1) = f (b_seq n))
    (hab : 0 < a ∧ a < b ∧ b < 1) :
    ∃ n : ℕ, 0 < n ∧ (a_seq n - a_seq (n - 1)) * (b_seq n - b_seq (n - 1)) < 0 := by
  -- Note first that all $a_{n}$ and $b_{n}$ lie in $(0,1)$.
  have ha_range : ∀ n, 0 < a_seq n ∧ a_seq n < 1 := by
    intro n
    induction n with
    | zero =>
      simp only [ha, h_a0]
      exact ⟨hab.left, by linarith⟩
    | succ n hn =>
      simp only [ha]
      constructor
      · by_cases h : a_seq n < 1 / 2
        · simp only [hf (a_seq n) h]
          linarith
        · push_neg at h
          simp only [hf' (a_seq n) h]
          nlinarith
      · by_cases h : a_seq n < 1 / 2
        · simp only [hf (a_seq n) h]
          linarith
        · push_neg at h
          simp only [hf' (a_seq n) h]
          nlinarith

  have hb_range : ∀ n, 0 < b_seq n ∧ b_seq n < 1 := by
    intro n
    induction n with
    | zero =>
      simp only [hb, h_b0]
      exact ⟨by linarith, hab.right.right⟩
    | succ n hn =>
      simp only [hb]
      constructor
      · by_cases h : b_seq n < 1 / 2
        · simp only [hf (b_seq n) h]
          linarith
        · push_neg at h
          simp only [hf' (b_seq n) h]
          nlinarith
      · by_cases h : b_seq n < 1 / 2
        · simp only [hf (b_seq n) h]
          linarith
        · push_neg at h
          simp only [hf' (b_seq n) h]
          nlinarith
  -- And unpacked
  have ha_range_lo : ∀ n, 0 < a_seq n := by
    exact fun n => (ha_range n).left
  have ha_range_hi : ∀ n, a_seq n < 1 := by
    exact fun n => (ha_range n).right
  have hb_range_lo : ∀ n, 0 < b_seq n := by
    exact fun n => (hb_range n).left
  have hb_range_hi : ∀ n, b_seq n < 1 := by
    exact fun n => (hb_range n).right
  -- Note that $f(x)-x=\frac{1}{2}>0$ if $x<\frac{1}{2}$ and $f(x)-x=x^{2}-x<0$ if $x \geq \frac{1}{2}$.
  have h1 : ∀ x, x < 1 / 2 -> 0 < f x - x := by
    intro x hx
    simp only [hf, hx]
    linarith
  have h2 : ∀ x, 1 /2 ≤ x -> x < 1 -> f x - x < 0 := by
    intro x hx
    simp only [hf', hx]
    intro hx'
    nlinarith
  -- And in the range $(0,1)$, this is iff
  have h1' : ∀ x, 0 < x -> x < 1 -> (x < 1 / 2 ↔ f x - x > 0 ):= by
    intros x
    intros hx0 hx1
    constructor
    · exact fun a ↦ h1 x a
    · simp only [gt_iff_lt]
      intro hf''
      contrapose! hf''
      exact le_of_lt (h2 x hf'' hx1)
  have h2' : ∀ x, 0 < x -> x < 1 -> (1 / 2 ≤ x ↔ f x - x < 0) := by
    intros x
    intros hx0 hx1
    constructor
    · exact fun a ↦ h2 x a hx1
    · intro hf''
      contrapose! hf''
      exact le_of_lt (h1 x hf'')
  -- thus, a_seq n < f (a_seq n) iff a_seq n < 1 / 2
  have h3 : ∀ n, f (a_seq n) - a_seq n > 0 ↔ a_seq n < 1 / 2 := by
    intro n
    rw [<-h1']
    exact ha_range_lo n
    exact ha_range_hi n
  have h4 : ∀ n, f (b_seq n) - (b_seq n) < 0 ↔ b_seq n ≥ 1 / 2 := by
    intro n
    rw [<-h2']

    exact hb_range_lo n
    exact hb_range_hi n

  have h3' : ∀ n, f (b_seq n) - b_seq n > 0 ↔ b_seq n < 1 / 2 := by
    intro n
    rw [<-h1']
    exact hb_range_lo n
    exact hb_range_hi n
  have h4' : ∀ n, f (a_seq n) - (a_seq n) < 0 ↔ a_seq n ≥ 1 / 2 := by
    intro n
    rw [<-h2']

    exact ha_range_lo n
    exact ha_range_hi n

  -- So if we consider $(0,1)$ as being divided into the two subintervals $I_{1}=\left(0, \frac{1}{2}\right)$ and $I_{2}=\left[\frac{1}{2}, 1\right)$, the inequality $\left(a_{n}-a_{n-1}\right)\left(b_{n}-b_{n-1}\right)=\left(f\left(a_{n-1}\right)-a_{n-1}\right)\left(f\left(b_{n-1}\right)-b_{n-1}\right)<0$ holds if and only if $a_{n-1}$ and $b_{n-1}$ lie in distinct subintervals.
  simp only [mul_neg_iff]
  -- Let us now assume, to the contrary, that $a_{k}$ and $b_{k}$ always lie in the same subinterval.
  by_contra h_contra
  rw [not_exists] at h_contra
  -- We rephrase the condition in terms of n+1
  have h_contra' := fun n => h_contra (n + 1)
  clear h_contra

  simp only [ha, hb] at h_contra'
  simp only [add_tsub_cancel_right, zero_add] at h_contra'
  simp only [h3,h4,h3',h4'] at h_contra'

  simp only [lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, ge_iff_le, true_and,
    not_or, not_and, not_le, not_lt] at h_contra'
  -- We split the h_contr' into two cases
  have h_contra1 := fun n => (h_contra' n ).left
  have h_contra2 := fun n => (h_contra' n ).right

  -- Consider the distance $d_{k}=\left|a_{k}-b_{k}\right|$.
  let d (k : ℕ) := abs (a_seq k - b_seq k)
  -- If both $a_{k}$ and $b_{k}$ lie in $I_{1}$,
  -- then $$ d_{k+1}=\left|a_{k+1}-b_{k+1}\right|=\left|a_{k}+\frac{1}{2}-b_{k}-\frac{1}{2}\right|=d_{k} $$
  have hd1 : ∀ k, a_seq k < 1 / 2 → b_seq k < 1 / 2 → d (k + 1) = d k := by
    intros k ha' hb'
    calc
      d (k + 1) = abs (f (a_seq k) - f (b_seq k)) := by simp [d, ha, hb]
      _ = abs (a_seq k + 1 / 2 - b_seq k - 1 / 2) := by
        congr 1
        simp only [hf, ha', hb']
        ring
      _ = abs (a_seq k - b_seq k) := by
        congr 1
        ring
      _ = d k := by
        simp [d]
  -- If, on the other hand, $a_{k}$ and $b_{k}$ both lie in $I_{2}$,
  -- then $\min \left(a_{k}, b_{k}\right) \geqslant \frac{1}{2}$ and $\max \left(a_{k}, b_{k}\right)=$ $\min \left(a_{k}, b_{k}\right)+d_{k} \geqslant \frac{1}{2}+d_{k}$,
  have max_eq_min_add_d : ∀ k, 1 / 2 ≤ a_seq k → 1 / 2 ≤ b_seq k → max (a_seq k) (b_seq k) = min (a_seq k) (b_seq k) + d k := by
    intros k ha' hb'
    unfold d
    have := max_sub_min_eq_abs' (a_seq k) (b_seq k)

    exact Eq.symm (add_eq_of_eq_sub' (id (Eq.symm this)))

  -- which implies (a_k + b_k) = min (a_k, b_k) + max (a_k, b_k) = 1 / 2 + 1/2 + d k
  have hd2 : ∀ k, 1 / 2 ≤ a_seq k → 1 / 2 ≤ b_seq k → a_seq k + b_seq k ≥ 1 / 2 + (1 / 2 + d k) := by
    intros k ha' hb'
    calc
      a_seq k + b_seq k = min (a_seq k) (b_seq k) + max (a_seq k) (b_seq k) := by
        exact Eq.symm (min_add_max (a_seq k) (b_seq k))
      _ ≥ 1 / 2 + (1 / 2 + d k) := by
        refine add_le_add ?_ ?_
        · simp only [le_inf_iff]
          exact ⟨ha', hb'⟩
        · rw [max_eq_min_add_d k ha' hb']
          simp only [ add_le_add_iff_right, le_inf_iff]
          exact ⟨ha', hb'⟩
  -- and so we have
  -- $$ d_{k+1}=\left|a_{k+1}-b_{k+1}\right|=\left|a_{k}^{2}-b_{k}^{2}\right|=\left|\left(a_{k}-b_{k}\right)\left(a_{k}+b_{k}\right)\right| \geqslant\left|a_{k}-b_{k}\right|\left(\frac{1}{2}+\frac{1}{2}+d_{k}\right)=d_{k}\left(1+d_{k}\right) \geqslant d_{k} $$
  have hd3 : ∀ k, 1 / 2 ≤ a_seq k → 1 / 2 ≤ b_seq k → d (k + 1) ≥ d k * (1 + d k) := by
    intros k ha' hb'
    calc
      d (k + 1) = abs (f (a_seq k) - f (b_seq k)) := by simp [d, ha, hb]
      _ = abs (a_seq k ^ 2 - b_seq k ^ 2) := by
        congr 1
        simp only [hf', ha', hb']
      _ = abs ((a_seq k - b_seq k) * (a_seq k + b_seq k)) := by
        congr 1
        ring
      _ = abs (a_seq k - b_seq k) * abs (a_seq k + b_seq k) := by
        rw [abs_mul]
      _ ≥ abs (a_seq k - b_seq k) * (1 / 2 + (1 / 2 + d k)) := by
        apply mul_le_mul_of_nonneg_left
        rw [abs_of_nonneg]
        apply hd2
        exact ha'
        exact hb'
        linarith
        exact abs_nonneg (a_seq k - b_seq k)
      _ = d k * (1 + d k) := by
        congr 1
        ring
  -- This means that the difference $d_{k}$ is non-decreasing,
  have hd_nondec : ∀ k, d k ≤ d (k + 1) := by
    intro k
    by_cases h : 1 / 2 ≤ a_seq k
    · have h' : 1 / 2 ≤ b_seq k := by
        exact h_contra2 k h
      have := hd3 k h h'
      apply le_trans _ this
      have : 0 ≤ d k := by exact abs_nonneg (a_seq k - b_seq k)
      nlinarith
    · push_neg at h
      have h' : b_seq k < 1 / 2 := by
        exact h_contra1 k h
      have := hd1 k h h'
      rw [this]

  -- and in particular $d_{k} \geqslant d_{0}&gt;0$ for all $k$.
  have hd_nondec' : ∀ k, d 0 ≤ d k := by
    intro k
    induction k with
    | zero =>
      exact Set.abs_sub_le_of_uIcc_subset_uIcc fun ⦃a⦄ a ↦ a
    | succ m hm =>
      apply le_trans hm
      exact hd_nondec m
  -- We can even say more.
  -- If $a_{k}$ and $b_{k}$ lie in $I_{2}$, then
  -- $$ d_{k+2} \geqslant d_{k+1} \geqslant d_{k}\left(1+d_{k}\right) \geqslant d_{k}\left(1+d_{0}\right) $$
  have hd4 : ∀ k, 1 / 2 ≤ a_seq k → 1 / 2 ≤ b_seq k → d (k + 2) ≥ d k * (1 + d 0) := by
    intros k ha' hb'
    calc
      d (k + 2) ≥ d (k + 1) := by
        exact hd_nondec (k + 1)
      _ ≥ d k * (1 + d k) := by
        exact hd3 k ha' hb'
      _ ≥ d k * (1 + d 0) := by
        apply mul_le_mul_of_nonneg_left
        simp
        exact hd_nondec' k
        exact abs_nonneg (a_seq k - b_seq k)
  -- If $a_{k}$ and $b_{k}$ both lie in $I_{1}$, then $a_{k+1}$ and $b_{k+1}$ both lie in $I_{2}$, and so we have
  -- $$ d_{k+2} \geqslant d_{k+1}\left(1+d_{k+1}\right) \geqslant d_{k+1}\left(1+d_{0}\right)=d_{k}\left(1+d_{0}\right) $$
  have hd1' : ∀ k, a_seq k < 1 / 2 → b_seq k < 1 / 2 → d (k + 2) ≥ d k * (1 + d 0) := by
    intros k ha' hb'
    have ha'' : 1 /2 ≤  a_seq (k + 1) := by
      simp only [ha, hf, ha']
      simp only [ le_add_iff_nonneg_left]
      exact le_of_lt (ha_range_lo k)
    have hb'' : 1 /2 ≤  b_seq (k + 1) := by
      exact h_contra2 (k + 1) ha''
    calc
      d (k + 2) ≥ d (k + 1) * (1 + d (k + 1)) := by
        exact hd3 (k + 1) ha'' (h_contra2 (k + 1) ha'')
      _ ≥ d (k + 1) * (1 + d 0) := by
        apply mul_le_mul_of_nonneg_left
        simp only [add_le_add_iff_left]
        exact hd_nondec' (k + 1)
        exact abs_nonneg (a_seq (k + 1) - b_seq (k + 1))
      _ ≥ d k * (1 + d 0) := by
        have : d k ≤ d (k + 1) := by
          exact hd_nondec k
        have this2 : 0 ≤ d 0 := by
          exact abs_nonneg (a_seq 0 - b_seq 0)
        apply mul_le_mul
        nlinarith
        exact (add_le_add_iff_left 1).mpr (hd_nondec' 0)
        positivity
        exact abs_nonneg (a_seq (k + 1) - b_seq (k + 1))
  -- In either case, $d_{k+2} \geqslant d_{k}\left(1+d_{0}\right)$,
  have hd_step : ∀ k, d (k + 2) ≥ d k * (1 + d 0) := by
    intro k
    by_cases h : 1 / 2 ≤ a_seq k
    · have h' : 1 / 2 ≤ b_seq k := by
        exact h_contra2 k h
      exact hd4 k h h'
    · push_neg at h
      have h' : b_seq k < 1 / 2 := by
        exact h_contra1 k h
      exact hd1' k h h'
  -- and inductively we get
  -- $$ d_{2 m} \geqslant d_{0}\left(1+d_{0}\right)^{m} $$
  have hd_ind : ∀ m, d (2 * m) ≥ d 0 * (1 + d 0) ^ m := by
    intro m
    induction m with
    | zero => simp only [mul_zero, pow_zero, mul_one, ge_iff_le, le_refl]
    | succ n ih =>
      simp [pow_succ]
      apply le_trans _ (hd_step (2 * n))
      rw [<-mul_assoc]
      apply mul_le_mul_of_nonneg_right
      exact ih
      positivity
  -- For sufficiently large $m$, the right-hand side is greater than 1
  have hd_lt : ∃ m, 1 < d 0 * (1 + d 0) ^ m := by
    have h0 : 0 < d 0 := by
      unfold d
      rw [h_a0, h_b0]
      rw [abs_sub_pos]
      linarith
    have h1 : 1 < 1 + d 0 := by
      linarith
    have : ∃ m, 1 / d 0 < (1 + d 0) ^ m := by
      have : ∀ r : ℝ, ∃ m, r < (1 + d 0) ^ m := by
        intro r
        exact pow_unbounded_of_one_lt r h1
      specialize this (1 / d 0)
      exact this
    rcases this with ⟨m, hm⟩
    use m
    exact (div_lt_iff₀' h0).mp hm
  rcases hd_lt with ⟨m, hm⟩
  -- but since $a_{2 m}, b_{2 m}$ both lie in $(0,1)$, we must have $d_{2 m}<1$, a contradiction.
  have hd_lt' : ∀ m, d (2 * m) ≤ 1 := by
    intro m
    unfold d
    rw [abs_le]
    have am_range_lo : 0 < a_seq (2 * m) := by
      exact ha_range_lo (2 * m)
    have am_range_hi : a_seq (2 * m) < 1 := by
      exact ha_range_hi (2 * m)
    have bm_range_lo : 0 < b_seq (2 * m) := by
      exact hb_range_lo (2 * m)
    have bm_range_hi : b_seq (2 * m) < 1 := by
      exact hb_range_hi (2 * m)
    constructor
    · linarith
    · linarith
  have hm' := hd_lt' m
  specialize hd_ind m
  linarith
