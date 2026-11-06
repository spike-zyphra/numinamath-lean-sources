import Mathlib

open Polynomial

/- C4. We call $(F, c)$ a good pair if the following three conditions are satisfied:
(1) $F(x)=a_{0}+a_{1} x+\cdots a_{m} x^{m},(m \geq 1)$ is a non-constant polynomial with integer coefficients.
(2) $c$ is a real number that is not an integer.
(3) $F(c)$ is an integer.

For example, both $\left(6 x, \frac{1}{3}\right)$ and $\left(1+x^{3}, 5^{1 / 3}\right)$ are good pairs, but none of the following pairs $\left(6 x, \frac{1}{4}\right)$, $(6 x, 2),\left(\frac{x}{6}, \frac{1}{3}\right),\left(\frac{x^{2}}{6}, 6\right)$ is good.
a. Let $c=\frac{1}{2}$. Give an example of $F$ such that $(F, c)$ is a good pair but $(F, c+1)$ is not.
b. Let $c=\sqrt{2}$. Give an example of $F$ such that both $(F, c)$ and $(F, c+1)$ are good pairs.
c. Show that for any good pair $(F, c)$, if $c$ is rational then there exists infinitely many non-zero integers $n$ such that $(F, c+n)$ is also a good pair.
d. Show that if $(F, c+n)$ is a good pair for every integer $n$, then $c$ is rational. -/

namespace number_theory_292012
def Good (F:ℤ[X]) (c:ℝ) := 1 ≤ F.natDegree ∧ (∃n:ℤ, n = Polynomial.aeval c F) ∧ ¬∃ n:ℤ, n = c

theorem number_theory_292012_1 : ∃ F, Good F (0.5) ∧ ¬Good F (1.5) := by
  -- With F= 2*X^3 + X^2 + X , we get F(0.5) = 1, F(1.5) = 21/2
  let F :ℤ[X] := 2*X^3 + X^2 + X
  use F
  constructor
  case left =>
    unfold Good
    constructorm* _ ∧ _
    case left =>
      have : F.natDegree = 3 := by unfold F ; compute_degree <;> trivial
      rw [this]
      trivial
    case right.left =>
      unfold aeval F
      norm_num
    case right.right =>
      simp
      intros z h
      have h₁ : z < 1 := by rify; linarith
      have h₂ : 0 < z := by rify; linarith
      linarith
  case right =>
    intro h
    obtain ⟨h_degree, ⟨n, h_eval⟩, h_int⟩ := h
    unfold aeval F at h_eval
    simp at h_eval
    norm_num at h_eval
    have h₁ : n < 11 := by rify; linarith
    have h₂ : 10 < n := by rify; linarith
    linarith

theorem number_theory_292012_2 : ∃ F, Good F √2 ∧ Good F (√2 + 1) := by
  -- With F = (X^2 - 2) * ((X-1)^2 - 2), we get F(√2) = F(√2+1) = 0
  let F:ℤ[X] := (X^2 - 2) * ((X-1)^2 - 2)
  use F
  have h_degree: F.natDegree = 4 := by unfold F; compute_degree <;> trivial
  constructor
  case left =>
    unfold Good
    constructorm* _ ∧ _
    case left =>
      rw [h_degree]
      trivial
    case right.left =>
      unfold aeval F
      simp
    case right.right =>
      simp
      intros z h
      have h₁ : z < 2 := by
        rify
        rw [h]
        have : 0 < √2 := by norm_num
        rw [← abs_of_pos this]
        apply abs_lt_of_sq_lt_sq <;> norm_num
      have h₂ : 1 < z := by
        rify
        rw [h]
        have : (0:ℝ) < 1 := by norm_num
        rw [← abs_of_pos this]
        apply abs_lt_of_sq_lt_sq <;> norm_num
      linarith
  case right =>
    unfold Good
    constructorm* _ ∧ _
    case left =>
      rw [h_degree]
      trivial
    case right.left =>
      have : F = ((X^2 - 2*X + 1) - 2) * (X^2 - 2) := by unfold F; ring_nf
      rw [this]
      unfold aeval
      simp
      use 0
      norm_num
      left
      ring_nf
      norm_num
    case right.right =>
      simp
      intros z h
      have h₁ : z < 3 := by
        rify
        rw [h]
        suffices : √2 < 2
        · linarith
        have : 0 < √2 := by norm_num
        rw [← abs_of_pos this]
        apply abs_lt_of_sq_lt_sq <;> norm_num
      have h₂ : 2 < z := by
        rify
        rw [h]
        suffices : 1 < √2
        · linarith
        have : (0:ℝ) < 1 := by norm_num
        rw [← abs_of_pos this]
        apply abs_lt_of_sq_lt_sq <;> norm_num
      linarith

theorem number_theory_292012_3 (F: ℤ[X]) (c:ℚ) (h_Fc : Good F c) : ∀ N:ℕ, ∃ n:ℤ, N < |n| ∧ Good F (c+n) := by
  -- For c = p/q, and k the degree of F, any multiple of q^k works
  -- For any N, (N+1)*q^k is bigger than N, since q^k > 0
  -- we call m = (N+1)*q^k
  intro N
  let k := F.natDegree
  use (N+1)*c.den^k
  obtain ⟨h_degree, ⟨n, h_eval⟩, h_int⟩ := h_Fc
  constructor
  case left =>
    have : 0 ≤ (N+1:ℤ) * c.den^k := by aesop
    rw [abs_of_nonneg this]
    norm_cast
    have : 0^k < c.den^k := by
      apply Nat.pow_lt_pow_left
      apply Rat.pos
      omega
    norm_num at this
    rw [Nat.zero_pow_of_pos] at this
    case h => linarith
    have : N = N * 1 := by simp
    rw [this]
    apply Nat.mul_lt_mul_of_lt_of_le <;> linarith
  case right =>
    unfold Good
    constructorm* _ ∧ _
    case left => assumption
    case right.left =>
      set m := ((N:ℤ) + 1) * ↑c.den ^ k
      -- let F(x) = ∑ a_i x^i, for i=0 to i=k
      -- the difference between F(c) and F(c+m) is ∑ a_i * (c+m)^i - c^i
      have h_F_diff : aeval (c + m:ℝ) F - (aeval (c:ℝ)) F =
          ∑ i ∈ Finset.range (k+1), F.coeff i • ((c+m)^i - c^i:ℝ) := by
        rw [Polynomial.aeval_eq_sum_range, Polynomial.aeval_eq_sum_range]
        rw [← Finset.sum_sub_distrib]
        unfold k
        congr
        ext i
        rw [zsmul_sub]
      -- the difference (c+n)^i - c^i = ∑ (i choose j) * (c^j * n) * n^(i-j-1) for j=0 to j=i-1
      have h_c_pow (n:ℤ) (i:ℕ) : ((c:ℝ)+n)^i - (c:ℝ)^i = ∑ j ∈ Finset.range i, Nat.choose i j * ((c:ℝ)^j * n) * n^(i-j-1) := by calc
        ((c:ℝ)+n)^i - c^i = ∑ j ∈ Finset.range (i + 1), (c:ℝ) ^ j * n ^ (i - j) * ↑(i.choose j) - c ^ i := by rw [add_pow]
        _ = ∑ j ∈ Finset.range i, (c:ℝ) ^ j * n ^ (i - j) * ↑(i.choose j) := by rw [Finset.sum_range_succ]; simp
        _ = _ := by
          have : ∀ j ∈ Finset.range i, (c:ℝ) ^ j * ↑n ^ (i - j) * ↑(i.choose j) = ↑(i.choose j) * (c ^ j * ↑n) * ↑n ^ (i - j - 1) := by
            intro j h
            ring_nf
            simp; left
            have : i-j ≠ 0:= Finset.mem_range_sub_ne_zero h
            rw [mul_assoc]
            rw [mul_pow_sub_one this (n:ℝ)]
          apply (Finset.sum_eq_sum_iff_of_le (by aesop)).mpr this
      -- continuing from the last equasion, it follows that for i≤k,
      -- (c+m)^i - c^i is an integer (since m is an integer, and the denominators in c^j cancel with q^k from m)
      have h_c_pow_int (i:ℕ) : i≤ k → ∃n:ℤ, n = ((c:ℝ)+(m:ℝ))^i - (c:ℝ)^i := by
        intro h_i
        rw [h_c_pow]
        use ∑ j∈ Finset.range i, i.choose j * (c.num^j * ((N+1) * c.den^(k-j))) * m^(i-j-1)
        push_cast
        have : ∀ j ∈ Finset.range i, (i.choose j :ℝ) * (↑c.num ^ j * ((↑N + 1) * ↑c.den ^ (k - j))) * ↑m ^ (i - j - 1) = ↑(i.choose j) * (↑c ^ j * ↑m) * ↑m ^ (i - j - 1) := by
          intro j h_j
          simp; left; left
          unfold m
          rw [pow_sub_of_lt _ ?lt]
          case lt => apply Finset.mem_range.mp at h_j; linarith
          calc (c.num:ℝ) ^ j * ((↑N + 1) * (↑c.den ^ k * (↑c.den ^ j)⁻¹)) = (c.num/c.den) ^ j * ((↑N + 1) * ↑c.den ^ k) := by ring
            _ = _ := by norm_cast; rw [Rat.divInt_self]
        apply (Finset.sum_eq_sum_iff_of_le ?leq).mpr this
        case leq => intro j h_j; exact le_of_eq (this j h_j)
      -- Combining this, the difference between F(c+m) and F(c) is an integer
      have h_diff_int : ∃ n':ℤ, n' = aeval (c + m:ℝ) F - (aeval (c:ℝ)) F := by
        rw [h_F_diff]
        have (n:ℕ) (f:ℕ→ℤ) (g:ℕ→ℝ) (h:∀i:ℕ, i<n → ∃m:ℤ, m = g i): ∃ z:ℤ, z = ∑ i ∈ Finset.range n, f i • g i := by
          induction n
          case zero => simp
          case succ n h_ind =>
            specialize h_ind ?req
            case req => intros i h'; apply h; linarith
            obtain ⟨z₁, h_ind⟩ := h_ind
            obtain ⟨z₂, h⟩ := h n (by linarith)
            use z₁ + f n • z₂
            simp
            rw [h, h_ind, Finset.sum_range_succ]
            simp
        apply this
        intro i h
        apply h_c_pow_int
        linarith
      -- so it follows that F(c+m) must be an integer)
      obtain ⟨n', h_diff_int⟩ := h_diff_int
      use n+n'
      push_cast
      linarith
    case right.right =>
      -- c+m is obviously not an integer, since c is not and m is
      intro h
      obtain ⟨n, h⟩ := h
      apply h_int
      use n - ((N+1) * c.den^k)
      push_cast
      rw [h]
      push_cast
      rw [add_sub_cancel_right]

theorem number_theory_292012_4 (F: ℤ[X]) (c: ℝ) (h_Fc : ∀ z:ℤ, Good F (c+z)) : ∃ q:ℚ, ↑q=c := by
  -- Assume otherwise, i.e. that c is irrrational
  by_contra h
  -- without loss of generality, we can assume that F is the polynomial with the minimal degree such that (F,c+z) is a good pair for all integers z
  let k := F.natDegree
  let P := fun i => ∃G:ℤ[X], natDegree G = i ∧ ∀n:ℤ, Good G (c+n)
  have exists_minimal (n:ℕ) (Pn: P n) : ∃n', Minimal P n' := by
    induction n using Nat.strong_induction_on
    case h n h_ind =>
      by_cases Minimal P n
      case pos => use n
      case neg h =>
        apply (exists_lt_of_not_minimal Pn) at h
        obtain ⟨k, lt, Pk⟩ := h
        apply h_ind k lt Pk
  wlog minimal_k : Minimal P k generalizing F
  · have Pk : P k := by unfold P; use F
    obtain ⟨n', min_n'⟩ := (exists_minimal k Pk)
    have Pn' := min_n'.prop
    obtain ⟨⟨G,G_degree, goodGc⟩ ,min_n'⟩ := min_n'
    apply this G goodGc
    rw [G_degree]
    constructor <;> assumption
  -- F cannot be linear, because then c would be rational
  have h_not_linear : 1 < k := by
    by_contra h_leq
    simp at h_leq
    specialize h_Fc 0; simp at h_Fc
    obtain ⟨h_F_degree, ⟨n, h_Fc_int⟩, _⟩ := h_Fc
    interval_cases hk: k
    case «0» => linarith
    case «1» =>
      have : F.degree = 1 := by
        unfold k at hk
        apply (degree_eq_iff_natDegree_eq_of_pos (by simp)).mpr at hk
        assumption
      have h_F := Polynomial.eq_X_add_C_of_degree_eq_one this
      rw [h_F] at h_Fc_int
      simp at h_Fc_int
      apply h
      exists (n - F.coeff 0)/F.leadingCoeff
      push_cast
      rw [h_Fc_int]
      simp
      apply mul_div_cancel_left₀
      norm_cast
      intro h
      apply Polynomial.leadingCoeff_eq_zero_iff_deg_eq_bot.mp at h
      rw [this] at h
      simp at h
  -- We look at G(x) = F(x+1) - F(x)
  let G : ℤ[X] := F.comp (X + C 1) - F
  -- Now the degree of G is less than the degree of F
  have : G.natDegree < k := by
    apply lt_of_le_of_ne ?le ?ne
    case le =>
      unfold G k
      have : (F.comp (X + C 1:ℤ[X])).natDegree ⊔ F.natDegree = F.natDegree := by
        apply Nat.max_eq_right
        have : (X+C 1:ℤ[X]).natDegree = 1 := by compute_degree; simp
        calc (F.comp (X + C 1)).natDegree ≤ F.natDegree * (X+C 1:ℤ[X]).natDegree := by apply natDegree_comp_le
          _ = F.natDegree := by rw [this]; simp
      rw [← this]
      apply natDegree_sub_le
    case ne =>
      intro h
      have pos : k > 0 := by linarith
      apply (degree_eq_iff_natDegree_eq_of_pos pos).mpr at h
      apply coeff_ne_zero_of_eq_degree at h
      apply h
      unfold G
      simp
      have h_k : k = F.natDegree * (X+1:ℤ[X]).natDegree := by
        unfold k
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · rw [natDegree_X]; simp
        · rw [natDegree_X, natDegree_one]; simp
      rw [h_k]
      rw [coeff_comp_degree_mul_degree ?deg_pos]
      rw [← h_k]
      unfold k
      simp
      rw [← C_1, leadingCoeff_X_add_C]
      simp
      case deg_pos =>
        rw [natDegree_add_eq_left_of_natDegree_lt]
        · rw [natDegree_X]; simp
        · rw [natDegree_X, natDegree_one]; simp
  -- Then (G,c+n) is a good pair for all integers n, since G(c+n) = F(c+n+1) - F(c+n) is an integer
  have PG : P G.natDegree := by
    unfold P
    use G
    constructor; simp
    intro n
    unfold Good
    have h_Fc1 := h_Fc (n+1)
    have h_Fc := h_Fc n
    constructorm* _ ∧ _
    case left =>
      suffices : k-1 ≤ G.natDegree
      · calc 1 ≤ k-1 := by omega
        _ ≤ G.natDegree := this
      apply Polynomial.le_natDegree_of_ne_zero
      unfold G
      simp
      nth_rw 1 [as_sum_range F]
      rw [sum_comp, finset_sum_coeff]
      simp
      have : ∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * ((X + 1:ℤ[X]) ^ i).coeff (k - 1)
          = ∑ i ∈ Finset.range (F.natDegree + 1), F.coeff i * ↑(i.choose (k-1)) := by
        congr; ext i
        rw [coeff_X_add_one_pow ℤ i (k-1)]
      rw [this]
      rw [Finset.sum_range_succ]
      have : F.natDegree = k - 1 + 1 := by
        unfold k
        rw [Nat.sub_one_add_one]
        omega
      nth_rw 1 [this]
      rw [Finset.sum_range_succ]
      simp
      have : ∑ x ∈ Finset.range (k - 1), F.coeff x * ↑(x.choose (k - 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp; right
        rw [Nat.choose_eq_zero_iff]
        apply Finset.mem_range.mp at hi
        assumption
      rw [this]
      group
      simp
      constructor
      case left =>
        intro h
        unfold k at h_not_linear
        rw [h] at h_not_linear
        simp at h_not_linear
      case right =>
        unfold k
        rw [Nat.choose_eq_zero_iff]
        simp
    case right.left =>
      obtain ⟨_,⟨z0, h_z0⟩ ,_⟩ := h_Fc
      obtain ⟨_,⟨z1, h_z1⟩,_⟩ := h_Fc1
      use z1-z0
      push_cast
      rw [h_z0,h_z1]
      unfold G
      simp
      rw [aeval_comp]
      rw [aeval_eq_sum_range, aeval_eq_sum_range, aeval_eq_sum_range]
      have : (X+1:ℤ[X]).natDegree = 1 := by compute_degree; simp
      rw [this]
      congr; ext i
      simp [Finset.sum_range_succ, coeff_one]
      left
      ring
    case right.right =>
      obtain ⟨_,_,this⟩ := h_Fc
      assumption
  -- So F is not minimal -> contradiction
  have : G.natDegree ≤ k := by linarith
  obtain ⟨_, minimal_k⟩ := minimal_k
  specialize minimal_k PG this
  linarith

end number_theory_292012