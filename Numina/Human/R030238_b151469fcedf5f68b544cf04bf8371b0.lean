import Mathlib

/- Find all positive integers $x, y$ satisfying the equation
$ 9\left(x^{2}+y^{2}+1\right)+2(3 x y+2)=2005 $ -/
theorem number_theory_604194 (x y : ℤ) (hx : x > 0) (hy : y > 0) :
  9 * (x ^ 2 + y ^ 2 + 1) + 2 * (3 * x * y + 2) = 2005 ↔ (x, y) = (11, 7) ∨ (x, y) = (7, 11) := by
  constructor
  intro h
  --The given equation can be written into the form $ 2(x+y)^{2}+(x-y)^{2}=664 $
  have : 9 * (x ^ 2 + y ^ 2 + 1) + 2 * (3 * x * y + 2) = 3 * (2 * (x + y) ^ 2 + (x - y) ^ 2) + 13:= by ring
  have this' : (2005 : ℤ) = 3 * 664 + 13 := by norm_num
  rw [this, this'] at h
  apply add_right_cancel at h
  apply mul_left_cancel₀ (by norm_num) at h
  -- Therefore, both numbers $x+y$ and $x-y$ are even.Let $x+y=2 m$ and $x-y=2 t, t \in \mathbb{Z}$.
  have even1 : Even (x - y) := by
    have : (x - y) ^ 2 = 664 - 2 * (x + y) ^ 2 := by rw [← h] ;ring
    have this' : 664 - 2 * (x + y) ^ 2  = 2 * (332 - (x + y) ^ 2 ) := by ring
    rw [this'] at this
    have : Even ((x - y) ^ 2) := by rw [this] ;simp
    apply Int.even_pow.mp at this ;exact this.1
  rcases even1 with ⟨t,ht⟩
  rw [ht,← two_mul,pow_two (2*t),mul_assoc,← mul_add] at h
  have : (664:ℤ) = 2 * 332 := by norm_num
  rw [this] at h
  apply mul_left_cancel₀ (by norm_num) at h
  have even2 : Even (x + y) := by
    have : (x + y) ^ 2 = 332 - t * (2 * t) := by rw [← h] ;ring
    have this' : 332 - t * (2 * t) = 2 * (166 - t ^ 2) := by ring
    rw [this'] at this
    have : Even ((x + y) ^ 2) := by rw [this] ;simp
    apply Int.even_pow.mp at this ;exact this.1
  rcases even2 with ⟨m,hm⟩
  rw [hm,← two_mul,pow_two (2*m),mul_assoc,mul_comm t,mul_assoc,← mul_add] at h
  have : (332:ℤ) = 2 * 166 := by norm_num
  rw [this] at h
  apply mul_left_cancel₀ (by norm_num) at h
  -- Now from (1) we have that $t$ and $t^{2}$ are even and $m$ is odd.
  have even3 : Even t := by
    have : t * t = 166 - 2 * (m * m) := by rw [← h] ;ring
    have this' : 166 - 2 * (m * m) = 2 * (83 - m * m) := by ring
    rw [this'] at this
    have : Even (t * t) := by rw [this] ;simp
    rw [← pow_two] at this ;apply Int.even_pow.mp at this ;exact this.1
  rcases even3 with ⟨k,hk⟩
  rw [hk,← two_mul,mul_comm,mul_assoc,mul_assoc,← mul_add] at h
  have : (166:ℤ) = 2 * 83 := by norm_num
  rw [this] at h
  apply mul_left_cancel₀ (by norm_num) at h
  have odd1 : Odd m := by
    have : m ^ 2 = 83 - 2 * k ^ 2 := by rw [← h] ;ring
    have this' : 83 - 2 * k ^ 2 = 2 * (41 - k ^ 2) + 1 := by ring
    rw [this'] at this
    have : Odd (m ^ 2) := by rw [this] ;simp
    apply Int.odd_pow.mp at this ;simp at this ;exact this
  -- So, if $t=2 k, k \in \mathbb{Z}$ and $m=2 n+1, n \in \mathbb{N}$, then from (1) we get $ k^2 = 41 - 2n(n+1) $.
  rcases odd1 with ⟨n,hn⟩
  rw [hn] at h
  have eq : 2 * k ^ 2 = 83 - 1 - 4 * n * (n + 1) := by rw [← h] ;ring
  have : 83 - 1 - 4 * n * (n + 1) = 2 * (41 - 2 * n * (n + 1)) := by ring
  rw [this] at eq
  apply mul_left_cancel₀ (by norm_num) at eq
  -- Thus $41-2 n(n+1) \geq 0$ or $2 n^{2}+2 n-41 \leq 0$. The last inequality is satisfied for the positive integers $n=1,2,3,4$ and for $n=0$.
  have h1 : 41 - 2 * n * (n + 1) ≥ 0 := by rw [← eq] ;exact sq_nonneg k
  simp at h1
  by_cases h2 : 5 ≤ n
  · have h3 : 2 * 5 * 6 ≤ 2 * n * (n + 1) := by
      apply Int.mul_le_mul ;apply Int.mul_le_mul ;norm_num ;exact h2 ;norm_num ;norm_num ;linarith ;linarith ;linarith
    linarith
  simp at h2
  have : m + m > 0 := by linarith
  have h3 : m > 0 := by linarith
  rw [hn] at this
  have : 0 ≤ n := by linarith
  -- However, only for $n=4$, equation (2) gives a perfect square $k^{2}=1 \Leftrightarrow k= \pm 1$.
  -- The following long section explains that when n < 4, k is not an integer, which is rather lengthy.
  have : (5:ℤ) = (((1+1)+1)+1) + 1 := by norm_num
  rw [this] at h2
  rcases (gt_or_eq_of_le (Int.lt_add_one_iff.mp h2)) with h|h
  · rcases (gt_or_eq_of_le (Int.lt_add_one_iff.mp h)) with h|h
    · rcases (gt_or_eq_of_le (Int.lt_add_one_iff.mp h)) with h|h
      · rcases (gt_or_eq_of_le (Int.lt_add_one_iff.mp h)) with h|h
        · have : n = 0 := by linarith
          simp [this] at eq
          have t1 : k ^ 2 > 6 ^ 2 := by linarith
          have t2 : k ^ 2 < 7 ^ 2 := by linarith
          apply lt_of_pow_lt_pow_left₀ at t1 ;apply lt_of_pow_lt_pow_left₀ at t2 ;linarith ;linarith ;linarith
        simp [← h] at eq
        have t1 : k ^ 2 > 6 ^ 2 := by linarith
        have t2 : k ^ 2 < 7 ^ 2 := by linarith
        by_cases t3 : 0 ≤ k
        · apply lt_of_pow_lt_pow_left₀ at t1
          apply lt_of_pow_lt_pow_left₀ at t2
          linarith ;linarith ;linarith
        have : 0 ≤ (-k) := by linarith
        have t1' : (-k) ^ 2 > 6 ^ 2 := by linarith
        have t2' : (-k) ^ 2 < 7 ^ 2 := by linarith
        apply lt_of_pow_lt_pow_left₀ at t1' ;apply lt_of_pow_lt_pow_left₀ at t2 ;linarith ;linarith ;linarith
      simp [← h] at eq
      have t1 : k ^ 2 > 5 ^ 2 := by linarith
      have t2 : k ^ 2 < 6 ^ 2 := by linarith
      by_cases t3 : 0 ≤ k
      · apply lt_of_pow_lt_pow_left₀ at t1
        apply lt_of_pow_lt_pow_left₀ at t2
        linarith ;linarith ;linarith
      have : 0 ≤ (-k) := by linarith
      have t1' : (-k) ^ 2 > 5 ^ 2 := by linarith
      have t2' : (-k) ^ 2 < 6 ^ 2 := by linarith
      apply lt_of_pow_lt_pow_left₀ at t1' ;apply lt_of_pow_lt_pow_left₀ at t2' ;linarith ;linarith ;linarith
    simp [← h] at eq
    have t1 : k ^ 2 > 4 ^ 2 := by linarith
    have t2 : k ^ 2 < 5 ^ 2 := by linarith
    by_cases t3 : 0 ≤ k
    · apply lt_of_pow_lt_pow_left₀ at t1
      apply lt_of_pow_lt_pow_left₀ at t2
      linarith ;linarith ;linarith
    have : 0 ≤ (-k) := by linarith
    have t1' : (-k) ^ 2 > 4 ^ 2 := by linarith
    have t2' : (-k) ^ 2 < 5 ^ 2 := by linarith
    apply lt_of_pow_lt_pow_left₀ at t1' ;apply lt_of_pow_lt_pow_left₀ at t2' ;linarith ;linarith ;linarith
  simp [← h] at eq
  -- Therefore the solutions are $(x, y)=(11,7)$ or $(x, y)=(7,11)$.
  rcases eq with eq|eq
  · simp [eq,hk] at ht
    simp [← h,hn] at hm
    have : 2 * x = (x + y) + (x - y) := by ring
    rw [ht,hm] at this
    have hx : 2 * x = 2 * 11 := by rw [this] ;norm_num
    apply mul_left_cancel₀ (by norm_num) at hx
    have : 2 * y = (x + y) - (x - y) := by ring
    rw [ht,hm] at this
    have hy : 2 * y = 2 * 7 := by rw [this] ;norm_num
    apply mul_left_cancel₀ (by norm_num) at hy
    simp [hx,hy]
  simp [eq,hk] at ht
  simp [← h,hn] at hm
  have : 2 * x = (x + y) + (x - y) := by ring
  rw [ht,hm] at this
  have hx : 2 * x = 2 * 7 := by rw [this] ;norm_num
  apply mul_left_cancel₀ (by norm_num) at hx
  have : 2 * y = (x + y) - (x - y) := by ring
  rw [ht,hm] at this
  have hy : 2 * y = 2 * 11 := by rw [this] ;norm_num
  apply mul_left_cancel₀ (by norm_num) at hy ;simp [hx,hy]
  -- The other direction is straightforward
  intro hxy
  rcases hxy with hxy|hxy
  · simp at hxy ;simp [hxy]
  simp at hxy ;simp [hxy]