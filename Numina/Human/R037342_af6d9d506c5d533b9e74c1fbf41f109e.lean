import Mathlib

/- 6. Given a sequence $\left\{a_{n}\right\}$ whose terms are all non-zero. Let the sum of the first $n$ terms of the sequence $\left\{a_{n}\right\}$ be $S_{n}$, and the sum of the first $n$ terms of the sequence $\left\{a_{n}^{2}\right\}$ be $T_{n}$, and $S_{n}^{2}+4 S_{n}-3 T_{n}=0\left(n \in \mathbf{Z}_{+}\right)$. Then the sum of the first $n$ terms of the sequence $\left\{\frac{(n-1)}{n(n+1)} a_{n}\right\}$ is $\qquad$ . -/
theorem algebra_120964 {a : ℕ → ℝ} (ha : ∀ n, a n ≠ 0)
    (S : ℕ → ℝ) (hS : ∀ n, S n = ∑ i in Finset.range n, a i)
    (T : ℕ → ℝ) (hT : ∀ n, T n = ∑ i in Finset.range n, (a i)^2)
    (hST : ∀ n, (S n)^2 + 4 * S n - 3 * T n = 0) :
    ∀ n, ∑ i in Finset.range n, a i * i / ((i + 1) * (i + 2)) =
    2^(n + 1) / (n + 1) - 2 := by

    -- do hST n.succ - hST n
    have h_rel : ∀ n, (S n.succ + S n + 4 - 3 * a n) * a n = 0 := by intro n; calc
      _ = (S n.succ + S n) * a n + 4 * a n - 3 * (a n)^2 := by ring
      _ = (S n.succ + S n) * (S n.succ - S n) + 4 * a n - 3 * (a n)^2 := by congr; rw [hS, Finset.sum_range_succ, ←hS]; exact (add_sub_cancel_left _ _).symm
      _ = (S n.succ)^2 - (S n)^2 + 4 * (S n.succ - S n) - 3 * (T n.succ - T n) := by
        congr
        · ring
        · rw [hS, Finset.sum_range_succ, ←hS]; exact (add_sub_cancel_left _ _).symm
        · rw [hT, Finset.sum_range_succ, ←hT]; exact (add_sub_cancel_left _ _).symm
      _ = ((S n.succ)^2 + 4 * S n.succ - 3 * T n.succ) - ((S n)^2 + 4 * S n - 3 * T n) := by ring
      _ = 0 := by rw [hST, hST]; exact zero_sub_zero

    -- cancel the a n from h_rel
    conv at h_rel => intro n; rw [mul_eq_zero_iff_right (ha n)]

    -- do h_rel n.succ - h_rel n
    have h_rel2 : ∀ n, - 2 * a n.succ + 4 * a n = 0 := by intro n; calc
      _ = (a n.succ + a n) - 3 * a n.succ + 3 * a n := by ring
      _ = (S (n + 2) - S n) - 3 * a n.succ + 3 * a n := by congr 2; rw [hS, Finset.sum_range_succ, hS, Finset.sum_range_succ]; ring
      _ = (S (n + 2) + S n.succ + 4 - 3 * a n.succ) - (S n.succ + S n + 4 - 3 * a n) := by ring
      _ = 0 := by rw [h_rel, h_rel]; exact zero_sub_zero
    have h_rel2' : ∀ n, a n.succ = 2 * a n := by intro n; specialize h_rel2 n; linarith

    -- obtain formula for a
    have h_a : ∀ n, a n = 2^n.succ := by intro n; induction n with
    | zero =>
      -- show a 0 = 2 (base case)
      specialize hST 1
      rw [hS, hT] at hST
      simp at hST
      have : a 0 * (4 - 2 * a 0) = 0 := by calc
        _ = (a 0)^2 + 4 * a 0 - 3 * (a 0)^2  := by ring
        _ = 0 := hST
      rw [mul_eq_zero_iff_left (ha 0)] at this
      linarith
      -- induction step is trivial since a n.succ = 2 * a n
    | succ n ih => rw [h_rel2' n, ih]; exact (pow_succ' _ _).symm

    -- partial fractions and telescoping sum setup
    set f := (fun i : ℕ ↦ (2^i.succ / i.succ : ℝ)) with hf
    have h_frac : ∀ (i : ℕ), a i * i / ((i + 1) * (i + 2)) = f (i + 1) - f i := by intro i; rw [h_a i, hf]; field_simp; ring

    -- rewrite inside sum and conclude
    intro n
    conv_lhs => arg 2; ext i; rw [h_frac i]
    rw [show 2^(n+1) / (n + 1) = f n by rw [hf]; simp, show 2 = f 0 by rw [hf]; simp]
    exact Finset.sum_range_sub f n