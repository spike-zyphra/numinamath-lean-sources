import Mathlib

/- A parabola with equation $y=ax^2+bx+c$ has a vertical line of symmetry at $x=2$ and goes through the two points $(1,1)$ and $(4,-1)$. The quadratic $ax^2 + bx +c$  has two real roots. The greater root is $\sqrt{n}+2$. What is $n$? -/
theorem algebra_22113 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * (4 - x) ^ 2 + b * (4 - x) + c = a * x ^ 2 + b * x + c)
    (h1 : a * 1 ^ 2 + b * 1 + c = 1) (h2 : a * 4 ^ 2 + b * 4 + c = -1)
    (x1 x2 : ℝ)
    (root1: x1 > x2)
    (root2: a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0)
    (n: ℝ)
    (root3: x1 = Real.sqrt n + 2) : n = 5 / 2 := by
  simp at *
  -- solve a, b, c
  have h3 : -4 * a = b := by
    specialize h 0
    linarith
  rw [<- h3] at h1
  rw [<- h3] at h2
  ring_nf at h2
  rw [h2] at h1
  ring_nf at h1
  have h1 : a = -2/3 := by linarith
  rw [h1] at h3
  ring_nf at h3

  -- solve x1, x2
  have disc: discrim a b c = 40/9 := by
    rw [h1, <- h3, h2]
    unfold discrim
    ring_nf
  let s := (Real.sqrt 40) / 3
  have s2 : discrim a b c = s * s := by
    rw [disc]
    ring_nf
    simp
    ring_nf

  -- solve x1
  have x1p: a * (x1 * x1) + b * x1 + c = 0 := by rw [<- root2.1]; ring_nf
  rw [(quadratic_eq_zero_iff ha s2 x1), h1, <- h3] at x1p
  ring_nf at x1p

  -- solve x2
  have x2p: a * (x2 * x2) + b * x2 + c = 0 := by rw [<- root2.2]; ring_nf
  rw [(quadratic_eq_zero_iff ha s2 x2), h1, <- h3] at x2p
  ring_nf at x2p

  -- use x1 > x2
  match x1p with
  | Or.inl h => {
    -- x1 is the smaller root
    match x2p with
    | Or.inl h' => {
      -- x1, x2 is the smaller root
      linarith
    }
    | Or.inr h' => {
      -- x2 is the larger root
      -- x2 > x1
      rw [h, h'] at root1
      simp at root1
      ring_nf at root1
      linarith
    }
  }
  | Or.inr h => {
    -- x1 is the larger root
    match x2p with
    | Or.inl h' => {
      rw [h] at root3
      ring_nf at root3
      simp at root3

      have n_pos : 0 < n := by rw [<- Real.sqrt_pos, <- root3]; simp
      have n_pos : 0 ≤ n := le_of_lt n_pos
      rw [<- Real.sq_sqrt n_pos, <- root3]
      ring_nf
      simp
      ring_nf
    }
    | Or.inr h' => {
      -- x1, x2 is the larger root
      linarith
    }
  }
