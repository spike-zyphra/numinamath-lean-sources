import Mathlib
open Mathlib
/-- Soit $p$ un nombre premier. Trouver tous les entiers $n \geqslant 1$ tels que pour tout entier $a \geqslant 1$, si $a^{n}-1$ est divisible par $p$, alors $a^{n}-1$ est aussi divisible par $p^{2}$. -/
theorem number_theory_607566 (p : ℕ) (hp : Nat.Prime p) (n : ℕ) (hn : 1 ≤ n) : (∀ a, 1 ≤ a → p ∣ a^n - 1 → p^2 ∣ a^n - 1) ↔ p ∣ n := by
  by_cases sp : p ∣ n
  -- If \(p\mid n\), then the property holds
  · simp only [sp, iff_true]
    intros a ha hb
    /-
    1. **Reduction mod \(p\).**  
    Since \(n=p\,m\), by Fermat’s Little Theorem
    \[
    a^p \equiv a \pmod p
    \quad\Longrightarrow\quad
    a^{pm} = (a^p)^m \equiv a^m \pmod p.
    \]
    -/
    have md := @Nat.ModEq.pow_totient a p
    rw [Nat.totient_prime hp] at md
    have as : a ^ n - 1 ≡ 0 [MOD p] := by exact Nat.modEq_zero_iff_dvd.mpr hb
    have dw := Nat.ModEq.add_right 1 as
    have tn := Nat.pow_le_pow_left ha n
    simp only [one_pow] at tn
    norm_num at dw
    rw [(by omega : a ^ n - 1 + 1 = a^n)] at dw
    -- Nat.Prime.coprime_iff_not_dvd will be of use
    -- from a ^ n ≡ 1 [MOD p] we deduce that a.Coprime n
    have copr : a.Coprime p := by
      clear * - hn hp dw
      -- induction on n
      induction n with
      -- vacuously true
      | zero => norm_num at hn
      | succ k ih =>
        obtain rfl | jj : k = 0 ∨ 1 ≤ k := by omega
        -- base case
        · simp only [nonpos_iff_eq_zero, one_ne_zero, pow_zero, IsEmpty.forall_iff, zero_add,
          le_refl, pow_one] at *
          have int : ¬(p ∣ a) := by
            rw [← Nat.modEq_zero_iff_dvd]
            intro kk
            simp only [Nat.ModEq, Nat.zero_mod] at *
            rw [@Nat.mod_eq_of_lt 1 _ (by exact Nat.Prime.one_lt hp)] at dw
            omega
          rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd] <;> assumption
        -- induction step
        · rw [Nat.pow_succ] at dw
          have cp := Nat.coprime_of_mul_modEq_one _ dw
          rw [Nat.coprime_pow_left_iff (by linarith)] at cp
          exact cp
    have rs := md copr
    clear md
    -- now that we have a ^ (p - 1) ≡ 1 [MOD p], it's time to multiple both sides by p
    have ml := Nat.ModEq.mul_right a rs
    norm_num at ml
    conv at ml =>
      left; right
      rw [(by norm_num : a = a^1)]
    rw [← Nat.pow_add] at ml
    have lt : 1 ≤ p := by exact Nat.Prime.one_le hp
    rw [(by clear * - lt; omega : p - 1 + 1 = p)] at ml
    -- n = p * m
    obtain ⟨m, w⟩ := sp
    -- raise both sides to the m
    have nm := Nat.ModEq.pow m ml
    rw [← Nat.pow_mul, ←w] at nm
    -- subtract 1
    have coe : (↑(a ^ n : ℕ) : ℤ) ≡ (↑(a ^ m : ℕ) : ℤ) [ZMOD p] := by rw [Int.natCast_modEq_iff]; exact nm
    have nj := Int.ModEq.sub_right 1 coe
    push_cast at nj
    have tt := Nat.pow_le_pow_left ha m
    norm_num at tt
    have uncoe : a^n - 1 ≡ a^m - 1 [MOD p] := by
      rw [← Int.natCast_modEq_iff]
      push_cast [tn, tt]
      exact nj
    symm at as
    have br := Nat.ModEq.trans as uncoe
    have fc : p ∣ a ^ m - 1 := by exact Nat.dvd_of_mod_eq_zero (id (Nat.ModEq.symm br)) -- now we already have one factor
    -- next up we expose p in (a^n - 1) / (a^m - 1)
    have pd : a^(p * m) - 1 = (a^m - 1) * ∑ i ∈ Finset.range p, (a^(m*i)) := by
      clear * - ha
      induction p with
      | zero => norm_num
      | succ p ih =>
        simp only [Finset.sum_range_succ]
        -- we skillfully apply induction hypothesis and mul_comm
        rw [add_mul, one_mul, Nat.pow_add, mul_add, ← ih, mul_comm m p]
        have ss := Nat.pow_le_pow_left ha m
        have tt := Nat.pow_le_pow_left ha (p * m)
        norm_num at ss tt
        -- turn into integers so ring can solve the goal
        zify [ss, tt, (by nlinarith : a ^ (p * m) * a ^ m ≥ 1)]
        ring
    have am : a^m ≡ 1 [MOD p] := by 
      symm at nm
      exact Nat.ModEq.trans nm dw
    /- since \(a^m\equiv1\pmod p\), each term \(a^{km}\equiv1\pmod p\), so
     \[
     1 + a^m + a^{2m} + \cdots + a^{(p-1)m}
     \equiv 1 + 1 + \cdots + 1 
     = p
     \pmod p,
     \]
     hence \(p\) divides that second factor as well. -/
    have mi l : ∑ i ∈ Finset.range l, a ^ (m * i) ≡ l [MOD p] := by
      clear * - am
      induction l with
      | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact rfl
      | succ l ih =>
        rw [Finset.sum_range_succ]
        have ff := Nat.ModEq.pow l am
        norm_num at ff
        rw [← Nat.pow_mul] at ff
        have df := Nat.ModEq.add ih ff
        exact df
    have pl := mi p
    have dv : p ∣ ∑ i ∈ Finset.range p, a ^ (m * i) := by
      simp only [Nat.ModEq, Nat.mod_self] at pl
      omega
    -- combine them, we get p^2 ∣ a^n - 1
    rw [pow_two]
    obtain ⟨ra, wa⟩ := dv; obtain ⟨rb, wb⟩ := fc
    exists (ra * rb)
    rw [(by ring : p * p * (ra * rb) = (p * ra) * (p * rb)), ← wa, ← wb]
    rw [mul_comm, ← pd, w]
  -- If \(p\nmid n\), then the property fails
  · simp only [sp, iff_false, not_forall, Classical.not_imp]
    /- Assume \(p\nmid n\).  We exhibit an integer \(a\) for which
    \[
    p\mid a^n-1
    \quad\text{but}\quad
    p^2\nmid a^n-1.
    \]
    Take
    \[
    a = p+1.
    \] -/
    exists (p + 1), (by norm_num)
    /-
    1. **Divisibility by \(p\).**  By the Binomial Theorem,
    \[
    (p+1)^n = 1 + n\,p + \binom{n}{2}p^2 + \cdots + p^n,
    \]
    so 
    \[
    (p+1)^n -1 \equiv n\,p \pmod{p^2}.
    \]
    In particular,
    \[
    (p+1)^n -1 \equiv 0\pmod p,
    \]
    so \(p\mid (a^n-1)\). -/
    have y := Commute.add_pow (x := p) (y := 1) (by exact Commute.one_right p) n
    norm_num at y
    -- we take 1 out
    have decomp : Finset.range (n + 1) = {0} ∪ Finset.Ico 1 (n + 1) := by
      ext r
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      clear * -; omega
    rw [decomp, Finset.sum_union (by simp)] at y
    simp only [Finset.sum_singleton, pow_zero, Nat.choose_zero_right, mul_one] at y
    -- expose p
    have mg := Finset.sum_Ico_add (fun x => p^x * n.choose x) 0 n 1
    norm_num at mg
    simp only [← mg] at y
    simp_rw [pow_add] at y; norm_num at y
    simp_rw [mul_assoc] at y
    rw [← Finset.mul_sum] at y
    have qi := @Nat.pow_le_pow_left 1 (p + 1) (by norm_num) n
    norm_num at qi
    have ty : p ∣ (p + 1) ^ n - 1 := by
      exists (∑ i ∈ Finset.range n, p ^ i * n.choose (1 + i))
      omega
    -- done proving p is a divisor
    exists ty
    /- 2. **Failure of divisibility by \(p^2\).**  Since \(p\nmid n\), the term \(n\,p\) is not divisible by \(p^2\).  Hence
    \[
    (p+1)^n -1 \equiv n\,p \not\equiv 0\pmod{p^2},
    \]
    which shows \(p^2\nmid (a^n-1)\).

    Thus when \(p\nmid n\) the implication “\(p\mid a^n-1\)\(\implies\)\(p^2\mid a^n-1\)” fails (witness \(a=p+1\)). -/
    have dc : Finset.range n = {0} ∪ Finset.Ico 1 n := by
      ext r
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico]
      omega
    rw [dc, Finset.sum_union (by simp)] at y
    simp only [Finset.sum_singleton, pow_one, Nat.choose_one_right] at y
    norm_num at y
    have lf : (p + 1) ^ n - 1 = p * n + p * ∑ x ∈ Finset.Ico 1 n, p ^ x * n.choose (1 + x) := by
      zify [qi]; linarith
    have ww := Finset.sum_Ico_add (fun x => p^x * n.choose (1 + x)) 0 (n - 1) 1
    rw [(by clear * - hn; omega : n - 1 + 1 = n)] at ww
    norm_num at ww
    simp_rw [pow_add, mul_assoc] at ww
    norm_num at ww
    rw [← Finset.mul_sum] at ww
    rw [← ww] at lf
    have df : p * p ∣ p * (p * ∑ i ∈ Finset.range (n - 1), p ^ i * n.choose (1 + (1 + i))) := by
      exists ∑ i ∈ Finset.range (n - 1), p ^ i * n.choose (1 + (1 + i))
      ring
    rw [← Nat.mul_dvd_mul_iff_right (c := p) (by exact Nat.Prime.pos hp)] at sp
    intro j
    rw [pow_two] at j
    apply sp
    rw [lf] at j
    clear * - df j
    obtain ⟨ww, hh⟩ := df; obtain ⟨yy, oo⟩ := j
    exists yy - ww
    rw [Nat.mul_sub, ← hh, ← oo]
    ring_nf
    exact
      Eq.symm
        (Nat.add_sub_self_right (n * p)
          (p * (p * ∑ x ∈ Finset.range (n - 1), p ^ x * n.choose (1 + (1 + x)))))
