import Mathlib

/- Montrer qu'il existe une infinité de couples ( $\mathrm{m}, \mathrm{n}$ ) d'entiers distincts tels que $\mathrm{m}!n!$ soit un carré parfait. -/
theorem number_theory_607433 :
    ∀ N : ℕ, ∃ m n : ℕ,
      m > N ∧ n > N ∧ m ≠ n ∧ IsSquare (Nat.factorial m * Nat.factorial n) :=
by
  /-
   - One might be tempted to take $m=n$ to have $m!n!=(n!)^{2}$ and thus obtain a perfect square.
   - However, the statement requires $m \neq n$.
   - Despite this, we can already see a natural way to make perfect squares appear.
   - Suppose without loss of generality that $m > n$ (since $m!n! = n!m!$, swapping $(m, n)$ with $(n, m)$ poses no problem).
   - Then $m!n! = m \times (m-1) \times \ldots \times (n+1) \times n! \times n! = m \times \ldots \times (n+1) \times (n!)^{2}$.
   - Thus, $m!n!$ will be a perfect square if and only if $m \times \ldots \times (n+1)$ is a perfect square.
   - The simplest way to achieve this is to choose $m = n+1 = k^{2}$ for some integer $k$ ($k \geqslant 2$ since we want $m, n \geqslant 1$).
   - Indeed, we then have $\left(k^{2}\right)!\left(k^{2}-1\right)!=k^{2}\left(\left(k^{2}-1\right)!\right)^{2}=\left[k\left(k^{2}-1\right)!\right]^{2}$.
   - Finally, for every integer $k \geqslant 2$, $(m, n) = \left(k^{2}, k^{2}-1\right)$ works, which provides us with infinitely many solution pairs.
  -/

  -- As we said, every integer $k \geqslant 2$, $(m, n) = \left(k^{2}, k^{2}-1\right)$ works. Let us show that
  have H : ∀ x, let k := x + 2; IsSquare (Nat.factorial (k^2) * Nat.factorial (k^2 - 1)) := by
    intros x k
    simp [IsSquare]
    -- Remember k = x + 2,
    -- So when we induction on x, is actual induction on k but start by 2.
    induction x with
    | zero =>
        simp [k, Nat.factorial]
        use 12
    | succ x ih =>
        simp [k]
        let k' := x + 2
        have : x + 1 + 2 = k' + 1 := by rfl
        rw [this]
        have : (k' + 1)^2 = k'^2 + 2*k' + 1 := by ring_nf
        use (k' + 1) * (k' ^ 2 + 2 * k').factorial
        rw [this] 
        simp only [Nat.factorial]
        linarith
        
  -- Now back to the main theorem.
  intro N
  let k := N+2
  let m := k^2
  let n := k^2 - 1
  use m
  use n
  -- We have to prove some trivial points.
  constructor
  . simp[m,k]
    ring_nf
    calc
      _ < 4 + N := by simp
      _ ≤ 4 + N + 3 * N := by simp
      _ = 4 + N*4 := by linarith
      _ ≤ 4 + N * 4 + N^2 := by simp
  . constructor
    . simp [n, k]
      ring_nf
      have : 4 + N * 4 + N ^ 2 - 1 = 3 + N * 4 + N ^ 2 := by
        rw [Nat.sub_add_comm, Nat.sub_add_comm]
        . simp
        . calc
            _ ≤ 4 := by simp
            _ ≤ _ := by simp
      rw [this]
      calc
        _ < 3 + N := by simp
        _ ≤ 3 + N + 3 * N := by simp
        _ = 3 + N * 4 := by linarith
        _ ≤ 3 + N * 4 + N^2 := by simp
    . constructor
      . simp[m, n]
        have : k > 0 := by simp[k]
        have : k ^ 2 ≠ 0 := by
          revert this
          induction k with
          | zero => intro c; contradiction
          | succ k ih =>
              intro c
              ring_nf
              apply Nat.ne_of_gt
              calc
                _ < 1 := by simp
                _ ≤ 1 + k*2 := by simp
                _ ≤ _ := by simp
        revert this
        cases (k^2)
        . intro c; contradiction
        . intros _ c; simp at c
      . -- Finally, we can use our lemma.
        apply H
