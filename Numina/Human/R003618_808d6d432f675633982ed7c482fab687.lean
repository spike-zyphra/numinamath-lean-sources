import Mathlib

/- 15. Let the sequences $\left\{a_{n}\right\}$ and $\left\{b_{n}\right\}$ satisfy $a_{0}=1, b_{0}=0$ and

$$

\left\{\begin{array}{l}
a_{n-1}=7 a_{n}+6 b_{n}-3, \\
b_{n+1}=8 a_{n}+7 b_{n}-4, n=0,1,2 \cdots
\end{array}\right.

$$


Prove: $a_{n}(n=0,1,2, \cdots)$ is a perfect square. -/

def c :ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n'+2 => 4 * (c (n'+1)) - c n'
theorem algebra_202115 {a b : ℕ → ℤ} (ha0 : a 0 = 1) (hb0 : b 0 = 0)
    (han : ∀ n, a (n + 1) = 7 * a n + 6 * b n - 3) (hbn : ∀ n, b (n + 1) = 8 * a n + 7 * b n - 4) :
    ∀ n, IsSquare (a n) := by
  -- we first compute a 1 and b 1
  have : a 1 = 4 ∧ b 1 = 4 := by
    have ha1 : a 1 = 7 * a 0 + 6 * b 0 - 3 := han 0
    rw [ha0, hb0] at ha1
    have ha1' : a 1 = 4 := by
      norm_num at ha1 ⊢
      exact ha1

    have hb1 : b 1 = 8 * a 0 + 7 * b 0 - 4 := hbn 0
    rw [ha0, hb0] at hb1
    have hb1' : b 1 = 4 := by
      norm_num at hb1 ⊢
      exact hb1

    exact ⟨ha1', hb1'⟩
  obtain ⟨ha1, hb1⟩ := this
  have h1:∀n>0, a (n+1) = 14*(a n) - (a (n-1)) - 6 := by
    intro n hn
    have h2:= han n
    rw [show b n = b (n-1+1) by apply congr_arg; omega, hbn (n-1)] at h2
    ring_nf at h2
    specialize han (n-1); apply congr_arg (fun t =>t*7) at han
    rw [show n-1+1 = n by omega] at han; ring_nf at han; apply congr_arg (fun t=>t+21-49*(a (n-1))) at han; ring_nf at han
    rw [← han] at h2; ring_nf at h2
    ring_nf; linarith
  -- by manually computing a n we get a 0 = 1^2, a 1 = 2^2, a 2 = 7^2. Let's guess a_n = c_n^2
  -- with c0=1, c1=2, c2=7 and c_(n+1) = 4*c_n-c_(n-1)
  let q:∃ c:ℕ → ℤ, c 0 = 1 ∧ c 1 = 2 ∧ c 2 = 7 ∧ ∀n>0, c (n+1) = 4*(c n) - c (n-1) := by
    use c
    simp
    constructor
    unfold c; simp
    constructor
    unfold c; simp
    constructor
    unfold c; simp
    unfold c; simp
    intro n hn
    conv_lhs => unfold c
    split
    · case _ n' hn' => omega
    · case _ n' hn' => omega
    · case _ n' n'' hn'' => simp at hn''; rw [hn'']; simp
  obtain ⟨c, ⟨c0, ⟨c1, ⟨c2, cdef⟩⟩⟩⟩ := q
  -- let there be a sequence d defined by d n = (c n)^2
  let q:∃ d:ℕ → ℤ, ∀n, d n = (c n)^2 := by
    use fun n => (c n)^2
    intro n; simp
  obtain ⟨d, d_def⟩ := q
  -- let's show d has the same recursive relation as a
  have hd: ∀n>0, d (n+1) = 14*(d n) - (d (n-1)) - 6 := by
    intro n hn
    rw [d_def, cdef n hn, show (4 * c n - c (n - 1)) ^ 2 = 14*(c n)^2-(c (n-1))^2-6-2*(4*(c n)*(c (n-1)) - (c n)^2 - (c (n-1))^2-3) by ring_nf,
        d_def, d_def
    ]
    simp
    rw [show (c n)^2=(c n)*(c n) by ring]
    -- this can be shown by induction
    induction n, hn using Nat.le_induction
    case base => simp [c0, c1, c2]
    case succ n hn hmn =>
      simp
      rw(config := { occs := .pos [3]}) [cdef n hn]; ring_nf
      rw [show 1+n=n+1 by ring, cdef n (by linarith)]; ring_nf at hmn ⊢
      linarith
  -- therefore d n = a n
  have hdn: ∀n, d n = a n := by
    intro n
    induction n using Nat.twoStepInduction
    case zero => rw [ha0, d_def, c0]; norm_num
    case one => rw [ha1, d_def, c1]; norm_num
    case more n' hmn hn' =>
      rw [h1 (n'+1) (by omega), hd (n'+1) (by linarith), show n'+1-1=n' by omega]
      linarith
  -- now trivial
  intro n
  unfold IsSquare
  use c n
  rw [← hdn n, d_def n]; ring_nf