import Mathlib

/- f is the function defined in the problem, it takes a tuple of three integers and returns a tuple of three integers. -/
def f : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
| (x, y, z) => (y + z - x, z + x - y, x + y - z)

/- Let's define a sequence q that will be used to express the iterated function f^[n]. -/
def q : ℕ → ℤ
| 0 => 0
| n + 1 => 1 - 2 * q n

/- The following lemma expresses the iterated function f^[n] in terms of the sequence q. -/
lemma lemma_1 (n : ℕ) (x y z : ℤ) :
    f^[n] (x, y, z) = (q n * y + q n * z + (1 - 2 * q n) * x, q n * z + q n * x + (1 - 2 * q n) * y, q n * x + q n * y + (1 - 2 * q n) * z) := by
  -- We can prove this by induction on n.
  induction n with
  | zero => simp [q]
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, ih, q, f]
    ring_nf

/- The following lemma calculates the value of q n. -/
lemma lemma_2 (n : ℕ) :
    3 * q n = 1 - (-2) ^ n := by
  -- We can prove this by induction on n.
  induction n with
  | zero => simp [q]
  | succ n ih =>
    simp [q, pow_succ]
    linear_combination -2 * ih

/- Gegeven is een drietal verschillende positieve gehele getallen $(a, b, c)$ met $a+b+c=2013$. Een stap bestaat uit het vervangen van het drietal $(x, y, z)$ door het drietal $(y+z-x, z+x-y, x+y-z)$. Bewijs dat we uitgaande van het drietal $(a, b, c)$ na 10 stappen een drietal krijgen dat minstens één negatief getal bevat. -/
theorem number_theory_604962 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h : a + b + c = 2013) :
    let (x, y, z) := f^[10] (a, b, c);
    x < 0 ∨ y < 0 ∨ z < 0 := by
  -- Let's first express the iterated function f^[10] in terms of the sequence q.
  simp [lemma_1]
  -- We can now calculate the value of q 10.
  rw [show q 10 = -341 by linarith only [lemma_2 10]]
  -- We can now prove the theorem by contradiction.
  by_contra! H
  -- We can now assume that x, y and z are all positive.
  rcases H with ⟨H₁, H₂, H₃⟩
  -- The difference between y and z is (-2) ^ 10 * (b - c) ≤ 2013, so the difference between b and c is at most 1.
  -- The same for other pairs of variables.
  have h₁ : b - c ≤ 1 := by linarith
  have h₂ : c - a ≤ 1 := by linarith
  have h₃ : a - b ≤ 1 := by linarith
  have h₄ : b - a ≤ 1 := by linarith
  have h₅ : c - b ≤ 1 := by linarith
  have h₆ : a - c ≤ 1 := by linarith
  -- It clearly contradicts the assumption that a, b and c are distinct.
  clear h H₁ H₂ H₃ ha hb hc
  omega
