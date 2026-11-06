import Mathlib


open BigOperators Nat Finset List

/- Let $k_0$ and $N$ be natural numbers. Let $S_{k_0,N}$ be the set of integer exponents
$\{k_0, k_0+1, \ldots, k_0+N\}$.
Compute the sum $V = \sum_{x \in S_{k_0,N}} \sum_{y \in S_{k_0,N}} |2^x - 2^y|$,
where the sum is over exponents $x$ and $y$ from the set $S_{k_0,N}$.
Show that $V = 2^{k_0} \left( (N-2)2^{N+2} + 2N+8 \right)$. -/



-- define V' function, x, y ∈ Finset.range (N + 1), suppose x > y
@[simp]
def V' (n : ℕ) : ℚ :=
  match n with
  | 0 => 0
  -- add `n + 1`, this is equivalent to adding ∑ i ∈ range (n + 1), (2 ^ (n + 1) - 2 ^ i) to V' n
  | n + 1 => V' n + (n + 1) * 2 ^ (n + 1) - (∑ i ∈ range (n + 1), 2 ^ i)

-- prove ∑ i ∈ range (n + 1), 2 ^ i = 2 ^ (n + 1) - 1, this is part of V'
@[simp]
lemma sum_1 (n : ℕ) : ∑ i ∈ range (n + 1), 2 ^ i = 2 ^ (n + 1) - (1 : ℚ) := by
  induction' n with d hd
  .
    simp
    bound
  .
    rw [Finset.sum_range_succ]
    rw [hd]
    noncomm_ring

-- prove throuth induction method
@[simp]
lemma sum_V' (n : ℕ) : V' n = (n - 2) * 2 ^ (n + 1) + n + 4 := by
  induction' n with d hd
  .
    simp
    bound

  .
    unfold V'
    rw [hd]
    simp
    noncomm_ring



theorem number_theory_635295 (k0 N : ℕ) (V : ℕ → ℚ) (hV : V N = 2 ^ k0 * (2 * (V' N))) :
    V N = 2 ^ k0 * ((N - 2) * 2 ^ (N + 2) + 2 * N + (8 : ℚ)) := by

  /- 2 ^ k0 is a constant number, so it can be put outside,
  when x = y, V N = 0. And x y are symmetric, so we only need to specify case that x > y,
  named V' N, V N = V N = 2 ^ k0 * (2 * (V' N)) -/

  rw [hV]
  simp
  ring