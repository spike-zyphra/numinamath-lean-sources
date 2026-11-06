import Mathlib

/-Find the last two digits of $\left[(\sqrt{29}+\sqrt{21})^{1984}\right]$.-/
theorem number_theory_125129 : ⌊(√29 + √21) ^ 1984⌋ % 100 = 71 := by
  -- 令 $x=\sqrt{29}+\sqrt{21}, y=\sqrt{29}-\sqrt{21}$, 则
  -- $$ \begin{array}{l} x^{2}=50+2 \sqrt{609}, \\ y^{2}=50-2 \sqrt{609} . \end{array} $$
  let x := √29 + √21
  let y := √29 - √21
  -- 设 $a=x^{2}, \quad b=y^{2}$, 则有 $$ \begin{aligned} a+b & =100, \\ a b & =64 . \end{aligned} $$
  let a := x ^ 2
  let b := y ^ 2
  have h1 : a + b = 100 := by
    simp [a,b,x,y]
    ring_nf
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    norm_num
  have h2 : a * b = 64 := by
    simp [a,b,x,y]
    rw [add_sq,sub_sq,Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    ring_nf
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    norm_num
  -- 令 $S_{0}=a^{0}+b^{0}, S_{n}=a^{n}+b^{n}$, 则有 $$ \begin{aligned} S_{n} & =(a+b) S_{n-1}-a b S_{n-2} \\ & =100 S_{n-1}-64 S_{n-2} . \end{aligned} $$
  let S n := a ^ n + b ^ n
  have h3 : ∀ n, S (n + 2) = 100 * S (n + 1) - 64 * S n := by
    intro n
    simp [S]
    rw [← h1,← h2]
    ring_nf
  -- 因为 $S_{n}$ 是正整数, 所以 $$ \begin{array}{l} S_{n} \equiv 36 S_{n-2} \equiv 6^{2} S_{n-2} \equiv 6^{4} S_{n-4} \equiv \cdots \\ \equiv 6^{992} S_{n-992}(\bmod 100) \text {. } \\ \end{array} $$
  -- 即 $S_{992} \equiv 6^{992} S_{0}=2 \cdot 6^{992}(\bmod 100)$. 因为 $\quad 6^{4} \equiv 1296 \equiv-4 \quad(\bmod 100)$, 则 $$ S_{992} \equiv 2(-4)^{248} \equiv 2^{497} \equiv\left(2^{22}\right)^{22} \cdot 2^{13} \text {. } $$
  have h4 : ∀ n, ∃ m q : ℤ, S n = m ∧ S (n + 1) = q := by
    intro n
    induction n with
    | zero => 
      use 2, 100
      simp [S,h1]
      norm_num
    | succ n ih =>
      rcases ih with ⟨m, q, hm, hq⟩
      use q, 100 * q - 64 * m
      rw [hq,add_assoc]
      norm_num
      rw [h3,hm,hq]
  have h5 : ∀ n, ⌊S (2 * n)⌋ % 100 = 36 ^ n * 2 % 100 := by
    intro n
    induction n with
    | zero => 
      simp [S]
    | succ n ih =>
      specialize h4 (2 * n)
      rcases h4 with ⟨m, q, hm, hq⟩
      have : S (2 * (n + 1)) = ↑(100 * q - 64 * m) := by
        rw [mul_add,mul_one,h3,hq,hm] ;simp
      rw [this,Int.floor_intCast]
      rw [hm,Int.floor_intCast] at ih
      have : 100 * q - 64 * m = 100 * (q - m) + 36 * m := by ring_nf
      rw [this,Int.add_emod]
      simp
      rw [Int.mul_emod,ih,← Int.mul_emod]
      ring_nf
  have (a n : Int) (b : Nat) : a ^ b % n = (a % n) ^ b % n := by
    induction b with
    | zero => rfl
    | succ b ih => simp [Int.pow_succ, Int.mul_emod, ih]
  have h6 : ⌊S 992⌋ % 100 = (2 ^ 22) ^ 22 * 2 ^ 13 % 100 := by
    specialize h5 496
    rw [show 992=2*496 by ring_nf,h5]
    rw [show 496=2*248 by ring_nf,pow_mul]
    rw [Int.mul_emod,this]
    rw [show 36^2%100=(-4)%100 by norm_num,← this,← Int.mul_emod]
    rw [show (-4)^248 = 4^248 by simp]
    rw [show (4:ℤ)=2^2 by norm_num,← pow_mul,← pow_mul,← pow_add]
    rw [show 22*22+13=2*248+1 by norm_num,pow_add,pow_one]
  -- 由于 $$ 2^{22}=2^{2} \quad(\bmod 100), $$
  -- 则 $$ \begin{aligned} S_{992} & \equiv\left(2^{2}\right)^{22} \cdot 2^{13}=2^{44} \cdot 2^{13} \equiv\left(2^{2}\right)^{2} \cdot 2^{13} \\ & \equiv 2^{17} \equiv 4096 \times 32 \equiv 72 \quad(\bmod 100) . \end{aligned} $$
  -- 即 $S_{992}$ 的末两位数是 72 . 
  replace h6 : ⌊S 992⌋ % 100 = 72 := by
    rw [Int.mul_emod,this] at h6
    rw [show (2:ℤ)^22%100=(2^2) by norm_num,← pow_mul,mul_comm 2,pow_mul,this] at h6
    rw [show (2:ℤ)^22%100=(2^2) by norm_num] at h6
    simp at h6 ;exact h6
  -- 由于 $$ 0 < \sqrt{29}-\sqrt{21} < 1, $$
  -- 所以 $$ \begin{array}{l} 0 < (\sqrt{29}-\sqrt{21})^{1984} < 1 . \\ {\left[(\sqrt{29}+\sqrt{21})^{1984}\right]=S_{992}-1 .} \end{array} $$
  -- 其末两位数是 71 .
  have h7 : ⌊(√29 + √21) ^ 1984⌋ = ⌊S 992⌋ - 1 := by
    refine Int.floor_eq_iff.mpr ?_
    simp
    have : ↑⌊S 992⌋ = S 992 := by
      specialize h4 992
      rcases h4 with ⟨m, _, hm, _⟩
      rw [hm] ;simp
    rw [this]
    simp only [S,a,b,x,y]
    rw [← pow_mul,← pow_mul]
    norm_num
    refine pow_le_one₀ ?_ ?_
    simp ;norm_num
    simp
    refine Real.sqrt_le_iff.mpr ?_
    constructor
    apply add_nonneg (by simp)
    simp
    ring_nf
    rw [Real.sq_sqrt (by simp)]
    have : 4 < √21 := by
      refine (Real.lt_sqrt (by simp)).mpr ?_
      norm_num
    nlinarith
  rw [h7,Int.sub_emod,h6]
  simp

      
    
