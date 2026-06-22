import Mathlib
open Classical
open BigOperators

abbrev Vec (n : ℕ) := Fin n → ℝ
variable {n : ℕ}
variable (f : Vec n → ℝ)
def innerpro (x y : Vec n) : ℝ :=
  ∑ i : Fin n, x i * y i
lemma innerproSelfNonneg (x : Vec n) :
  innerpro x x ≥ 0 := by
  unfold innerpro
  exact Finset.sum_nonneg (by
    intro i hi
    nlinarith)

noncomputable def vnorm (x : Vec n) : ℝ := Real.sqrt (innerpro x x)
lemma vnorm_nonneg (x : Vec n) : 0 ≤ vnorm x := Real.sqrt_nonneg _

lemma vnorm_sq (x : Vec n) : (vnorm x)^2 = innerpro x x :=
  Real.sq_sqrt (innerproSelfNonneg x)

lemma cauchySchwarz (x y : Vec n) : innerpro x y ≤ vnorm x * vnorm y := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hxx : innerpro x x = ∑ i : Fin n, x i ^ 2 := by
    unfold innerpro; exact Finset.sum_congr rfl (by intro i _; ring)
  have hyy : innerpro y y = ∑ i : Fin n, y i ^ 2 := by
    unfold innerpro; exact Finset.sum_congr rfl (by intro i _; ring)
  have hprod : vnorm x * vnorm y = Real.sqrt (innerpro x x * innerpro y y) := by
    rw [vnorm, vnorm, ← Real.sqrt_mul (innerproSelfNonneg x)]
  rw [hprod]
  have h2 : (innerpro x y)^2 ≤ innerpro x x * innerpro y y := by
    rw [hxx, hyy]; exact hcs
  calc innerpro x y ≤ Real.sqrt ((innerpro x y)^2) := by
            rw [Real.sqrt_sq_eq_abs]; exact le_abs_self _
    _ ≤ Real.sqrt (innerpro x x * innerpro y y) := Real.sqrt_le_sqrt h2
lemma vnorm_neg (x : Vec n) : vnorm (-x) = vnorm x := by
  unfold vnorm innerpro; simp

lemma vnorm_smul (α : ℝ) (d : Vec n) :
    vnorm (fun i => α * d i) = |α| * vnorm d := by
  unfold vnorm innerpro
  have h : (∑ i : Fin n, (α * d i) * (α * d i)) = α^2 * ∑ i, d i * d i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (by intro i _; ring)
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
variable (grad : Vec n → Vec n)

def GradLipschitz (g : Vec n → Vec n) (L : ℝ) : Prop :=
  ∀ x y : Vec n,
    vnorm (g x - g y) ≤ L * vnorm (fun i => x i - y i)

def FirstOrderApprox (f : Vec n → ℝ) (g : Vec n → Vec n) : Prop :=
  ∀ (x d : Vec n) (c1 : ℝ), 0 < c1 → c1 < 1 → innerpro (g x) d < 0 →
    ∃ ε > 0,
      ∀ α ∈ Set.Ioo (0 : ℝ) ε,
        f (fun i => x i + α * d i)
          ≤ f x + c1 * α * innerpro (g x) d


-- part 3 : descent and line search conditions
def isDescentDirection (x d : Vec n) : Prop :=
  innerpro (grad x) d < 0
lemma negGradIsDescent (x : Vec n) :
  innerpro (grad x) (-grad x) ≤ 0 := by
  have h :
      innerpro (grad x) (-grad x)
        = - innerpro (grad x) (grad x) := by
    simp [innerpro]
  have h2 :
      innerpro (grad x) (grad x) ≥ 0 :=
    innerproSelfNonneg (grad x)
  have h3 :
      - innerpro (grad x) (grad x) ≤ 0 :=
    neg_nonpos.mpr h2
  simpa [h] using h3
lemma descentImpliesDecrease
  (x d : Vec n)
  (hdesc : isDescentDirection grad x d)
  (hfo : FirstOrderApprox f grad) :
  ∃ α > 0, f (fun i => x i + α * d i) < f x := by
  unfold isDescentDirection at hdesc
  obtain ⟨ε, hεpos, hε⟩ :=
    hfo x d (1 / 2) (by norm_num) (by norm_num) hdesc
  have hαpos : ε / 2 > 0 :=
    half_pos hεpos
  have hαrange :
      ε / 2 ∈ Set.Ioo (0 : ℝ) ε := by
    constructor
    · exact hαpos
    · have : ε / 2 < ε := by linarith
      exact this
  have hmain := hε (ε / 2) hαrange
  have hneg :
      (1 / 2) * (ε / 2) * innerpro (grad x) d < 0 := by
    have hpos : (0 : ℝ) < (1 / 2) * (ε / 2) := by positivity
    exact mul_neg_of_pos_of_neg hpos hdesc
  refine ⟨ε / 2, hαpos, ?_⟩
  linarith
-- armijo
def armijo (x d : Vec n) (α c1 : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c1 * α * innerpro (grad x) d
lemma existsArmijoStep
  (x d : Vec n) (c1 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hfo : FirstOrderApprox f grad) :
  ∃ α > 0, armijo f grad x d α c1 := by
  unfold isDescentDirection at hdesc
  obtain ⟨ε, hεpos, hε⟩ :=
    hfo x d c1 hc1.1 hc1.2 hdesc
  refine ⟨ε / 2, half_pos hεpos, ?_⟩
  exact hε (ε / 2) ⟨half_pos hεpos, by linarith⟩
-- backtracking
def backtrackStep (γ : ℝ) (α : ℝ) : ℝ :=
  γ * α
def backtrackPow (γ α0 : ℝ) (k : ℕ) : ℝ :=
  (γ ^ k) * α0
def existsBacktrackingStep
  (x d : Vec n) (c1 γ α0 : ℝ) : Prop :=
  ∃ k : ℕ,
    armijo f grad x d (backtrackPow γ α0 k) c1

def backtrackRun (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | k, 0        => k
  | k, fuel + 1 => if test k then k else backtrackRun test (k + 1) fuel

lemma backtrackRun_finds (test : ℕ → Bool) :
    ∀ (fuel k : ℕ),
      (∃ j, k ≤ j ∧ j < k + fuel ∧ test j = true) →
      test (backtrackRun test k fuel) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro k h
      obtain ⟨j, hkj, hjk, _⟩ := h
      exfalso; omega
  | succ fuel ih =>
      intro k h
      rw [backtrackRun]
      by_cases hk : test k = true
      · rw [if_pos hk]; exact hk
      · rw [if_neg hk]
        apply ih
        obtain ⟨j, hkj, hjk, htj⟩ := h
        refine ⟨j, ?_, by omega, htj⟩
        rcases Nat.eq_or_lt_of_le hkj with rfl | h'
        · exact absurd htj hk
        · omega

lemma backtrackingFindsStep
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) :
  ∃ k : ℕ,
    armijo f grad x d (backtrackPow γ α0 k) c1 := by
  obtain ⟨ε, hεpos, hε⟩ := hfo x d c1 hc1.1 hc1.2 hdesc
  -- Choose k such that the geometric step γ^k * α0 lands inside (0, ε).
  obtain ⟨k, hk⟩ : ∃ k : ℕ, γ ^ k * α0 < ε := by
    simpa using ( summable_geometric_of_lt_one hγ.1.le hγ.2 ) |> fun h => h.mul_right α0 |> fun h => h.tendsto_atTop_zero.eventually ( gt_mem_nhds hεpos ) |> fun h => h.exists
  refine ⟨k, ?_⟩
  unfold armijo backtrackPow
  exact hε (γ ^ k * α0) ⟨mul_pos (pow_pos hγ.1 _) hα0, hk⟩

noncomputable def btIndex
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) : ℕ :=
  Nat.find
    (backtrackingFindsStep
      f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo)

lemma btIndex_armijo
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) :
  armijo f grad x d
    (backtrackPow γ α0 (btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo)) c1 := by
  unfold btIndex
  exact Nat.find_spec
    (backtrackingFindsStep f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo)

lemma btIndex_least
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) :
  ∀ j < btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo,
    ¬ armijo f grad x d (backtrackPow γ α0 j) c1 := by
  intro j hj
  unfold btIndex at hj
  exact Nat.find_min
    (backtrackingFindsStep f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo) hj
noncomputable def btAlpha
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) : ℝ :=
  backtrackPow γ α0
    (btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo)
lemma btAlphaPos
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) :
  btAlpha f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo > 0 := by
  unfold btAlpha
  have hγpos : 0 < γ := hγ.1
  have hpow :
      0 < γ ^ (btIndex f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo) :=
    pow_pos hγpos _
  exact mul_pos hpow hα0

lemma btAlpha_armijo
  (x d : Vec n) (c1 γ α0 : ℝ)
  (hdesc : isDescentDirection grad x d)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hfo : FirstOrderApprox f grad) :
  armijo f grad x d
    (btAlpha f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo) c1 := by
  unfold btAlpha
  exact btIndex_armijo f grad x d c1 γ α0 hdesc hc1 hγ hα0 hfo
variable (x0 : Vec n)
def descent_dir (x : Vec n) : Vec n :=
  - grad x
def update (x d : Vec n) (α : ℝ) : Vec n :=
  fun i => x i + α * d i
noncomputable def next_x
  (x : Vec n) (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc : isDescentDirection grad x (-grad x))
  (hfo : FirstOrderApprox f grad) :
  Vec n :=
  update x (-grad x)
    (btAlpha f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0 hfo)
noncomputable def x_seq
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (hfo : FirstOrderApprox f grad) :
  ℕ → Vec n
| 0 => x0
| (k+1) =>
  let xk := x_seq c1 γ α0 hc1 hγ hα0 hdesc_all hfo k
  next_x f grad xk c1 γ α0 hc1 hγ hα0 (hdesc_all xk) hfo
termination_by k => k
lemma update_eq_fun (x d : Vec n) (α : ℝ) :
  update x d α = (fun i => x i + α * d i) :=
  rfl
lemma oneStepDescent
  (x : Vec n)
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc : isDescentDirection grad x (-grad x))
  (hfo : FirstOrderApprox f grad) :
  f (next_x f grad x c1 γ α0 hc1 hγ hα0 hdesc hfo)
  ≤ f x := by
  unfold next_x
  let α :=
    btAlpha f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0 hfo
  have hA :=
    btAlpha_armijo f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0 hfo
  unfold armijo at hA
  have hA' :
    f (fun i => x i + -(α * grad x i))
      ≤ f x + c1 * α * innerpro (grad x) (-grad x) := by
    simpa [α, neg_mul] using hA
  have hinner : innerpro (grad x) (-grad x) < 0 :=
    hdesc
  have hαpos :
    α > 0 :=
    btAlphaPos f grad x (-grad x) c1 γ α0 hdesc hc1 hγ hα0 hfo
  have hprod :
    c1 * α * innerpro (grad x) (-grad x) < 0 := by
    have h1 : 0 < c1 := hc1.1
    have h12 : 0 < c1 * α := mul_pos h1 hαpos
    exact mul_neg_of_pos_of_neg h12 hinner
  have hprod_le :
    c1 * α * innerpro (grad x) (-grad x) ≤ 0 :=
    le_of_lt hprod
  have hfinal :
    f (fun i => x i + -(α * grad x i)) ≤ f x := by
    have := hA'
    linarith
  rw [update_eq_fun]
  have hfinal' :
    f (fun i => x i + α * (-grad x i)) ≤ f x := by
    simpa [neg_mul] using hfinal
  exact hfinal'
def goldstein (x d : Vec n) (α c : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c * α * innerpro (grad x) d
  ∧
  f (fun i => x i + α * d i)
    ≥ f x + (1 - c) * α * innerpro (grad x) d
lemma goldsteinImpliesArmijo
  (x d : Vec n) (α c : ℝ)
  (h : goldstein f grad x d α c) :
  armijo f grad x d α c := by
  unfold goldstein at h
  unfold armijo
  exact h.1
lemma armijoImpliesStrictDecrease
  (x d : Vec n)
  (α c1 : ℝ)
  (hA : armijo f grad x d α c1)
  (hdesc : isDescentDirection grad x d)
  (hα : α > 0)
  (hc1 : c1 > 0) :
  f (fun i => x i + α * d i) < f x := by
  unfold armijo at hA
  unfold isDescentDirection at hdesc
  have hneg :
    c1 * α * innerpro (grad x) d < 0 := by
    have hpos : c1 * α > 0 := mul_pos hc1 hα
    exact mul_neg_of_pos_of_neg hpos hdesc
  have :
    f (fun i => x i + α * d i) < f x := by
    have := hA
    linarith
  exact this
def wolfe (x d : Vec n) (α c1 c2 : ℝ) : Prop :=
  f (fun i => x i + α * d i)
    ≤ f x + c1 * α * innerpro (grad x) d
  ∧
  innerpro (grad (fun i => x i + α * d i)) d
    ≥ c2 * innerpro (grad x) d
lemma innerpro_sub_left (x y d : Vec n) :
  innerpro (fun i => x i - y i) d
    = innerpro x d - innerpro y d := by
  unfold innerpro
  simp [sub_mul, Finset.sum_sub_distrib]
lemma wolfeImpliesArmijo
  (x d : Vec n) (α c1 c2 : ℝ)
  (h : wolfe f grad x d α c1 c2) :
  armijo f grad x d α c1 := by
  unfold wolfe at h
  unfold armijo
  exact h.1
lemma wolfeCurvatureIneqMain
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x d : Vec n) (α c1 c2 : ℝ)
  (h : wolfe f grad x d α c1 c2) :
  innerpro (grad (fun i => x i + α * d i) - grad x) d
    ≥ (c2 - 1) * innerpro (grad x) d := by
  unfold wolfe at h
  have hcurv :
    innerpro (grad (fun i => x i + α * d i)) d
      ≥ c2 * innerpro (grad x) d :=
    h.2
  have h1 :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      =
    innerpro (grad (fun i => x i + α * d i)) d
      - innerpro (grad x) d :=
    innerpro_sub_left _ _ _
  have h2 :
    innerpro (grad (fun i => x i + α * d i)) d
      - innerpro (grad x) d
    ≥
    c2 * innerpro (grad x) d
      - innerpro (grad x) d :=
    sub_le_sub_right hcurv _
  have h3 :
    c2 * innerpro (grad x) d
      - innerpro (grad x) d
    =
    (c2 - 1) * innerpro (grad x) d := by
    ring
  simpa [h1, h3] using h2

-- (add) part 4 : nonmonotone line search
def grippo
  (x_seq : ℕ → Vec n)
  (d_seq : ℕ → Vec n)
  (α_seq : ℕ → ℝ)
  (refval : ℕ → ℝ)
  (c1 : ℝ)
  (k : ℕ) : Prop :=
  f (x_seq (k + 1))
    ≤
  refval k
    +
  c1 * α_seq k *
      innerpro
        (grad (x_seq k))
        (d_seq k)
def qseq
  (η : ℝ) : ℕ → ℝ
| 0 => 1
| (k + 1) => η * qseq η k + 1
noncomputable def cseq
  (x_seq : ℕ → Vec n)
  (η : ℝ) : ℕ → ℝ
| 0 => f (x_seq 0)
| (k + 1) =>
    (
      η * (qseq η k) * (cseq x_seq η k)
      +
      f (x_seq (k + 1))
    )
    /
    (qseq η (k + 1))
def zhangHager
  (x_seq : ℕ → Vec n)
  (d_seq : ℕ → Vec n)
  (α_seq : ℕ → ℝ)
  (η c1 : ℝ)
  (k : ℕ) : Prop :=
  f (x_seq (k + 1))
    ≤
  cseq f x_seq η k
    +
  c1 * α_seq k *
        innerpro
          (grad (x_seq k))
          (d_seq k)
lemma qseqEtaZero :
  ∀ k : ℕ,
    qseq (0 : ℝ) k = 1
:= by
  intro k
  induction k with
  | zero =>
      simp [qseq]
  | succ k ih =>
      simp [qseq, ih]
lemma cseqEtaZero
  (x_seq : ℕ → Vec n) :
  ∀ k : ℕ,
    cseq f x_seq 0 k
      =
    f (x_seq k)
:= by
  intro k
  induction k with
  | zero =>
      simp [cseq]
  | succ k ih =>
      simp [cseq, qseqEtaZero, ih]
lemma zhangHagerEtaZero
  (x_seq : ℕ → Vec n)
  (d_seq : ℕ → Vec n)
  (α_seq : ℕ → ℝ)
  (c1 : ℝ)
  (k : ℕ)
  (hstep :
    x_seq (k + 1)
      =
    fun i =>
      x_seq k i + α_seq k * d_seq k i) :
  zhangHager f grad x_seq d_seq α_seq 0 c1 k
    ↔
  armijo
    f grad
    (x_seq k)
    (d_seq k)
    (α_seq k)
    c1
:= by
  unfold zhangHager
  unfold armijo
  rw [cseqEtaZero]
  constructor <;> intro h
  · simpa [hstep] using h
  · simpa [hstep] using h
lemma cseqConvex
  (x_seq : ℕ → Vec n)
  (η : ℝ)
  (k : ℕ) :
  cseq f x_seq η (k + 1)
    =
  (η * qseq η k / qseq η (k + 1))
      * cseq f x_seq η k
  +
  (1 / qseq η (k + 1))
      * f (x_seq (k + 1))
:= by
  simp [cseq]
  ring
lemma lipschitzUpperBound
  (x d : Vec n)
  (α L : ℝ)
  (hα : α ≥ 0)
  (hgradLip : GradLipschitz grad L) :
  innerpro (grad (fun i => x i + α * d i) - grad x) d
    ≤ L * α * (vnorm d)^2 := by
  have hlip :=
    hgradLip
      (fun i => x i + α * d i) x
  have hdiff :
    (fun i => (fun i => x i + α * d i) i - x i)
      =
    (fun i => α * d i) := by
    funext i
    simp
  have hlip' :
    vnorm (grad (fun i => x i + α * d i) - grad x)
      ≤ L * vnorm (fun i => α * d i) := by
    simpa [hdiff] using hlip
  have hnorm :
    vnorm (fun i => α * d i) = |α| * vnorm d :=
    vnorm_smul α d
  have hcs :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    vnorm (grad (fun i => x i + α * d i) - grad x)
      * vnorm d :=
    cauchySchwarz _ _
  have hcombine :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    (L * vnorm (fun i => α * d i)) * vnorm d := by
    have hnonneg : 0 ≤ vnorm d :=
      vnorm_nonneg d
    have hmul :
      vnorm (grad (fun i => x i + α * d i) - grad x) * vnorm d
        ≤
      (L * vnorm (fun i => α * d i)) * vnorm d :=
      mul_le_mul_of_nonneg_right hlip' hnonneg
    exact le_trans hcs hmul
  have hcombine' :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    (L * (|α| * vnorm d)) * vnorm d := by
    simpa [hnorm] using hcombine
  have hfinal :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤
    L * |α| * (vnorm d)^2 := by
    ring_nf at hcombine'
    simpa [pow_two] using hcombine'
  have habs : |α| = α :=
    abs_of_nonneg hα
  simpa [habs] using hfinal
lemma alpha_lower_bound_mul
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hα : α ≥ 0)
  (hw : wolfe f grad x d α c1 c2)
  (hgradLip : GradLipschitz grad L) :
  (c2 - 1) * innerpro (grad x) d
    ≤ L * α * (vnorm d)^2 := by
  have h1 :
    (c2 - 1) * innerpro (grad x) d
      ≤ innerpro (grad (fun i => x i + α * d i) - grad x) d := by
    exact
      wolfeCurvatureIneqMain f grad x d α c1 c2 hw
  have h2 :
    innerpro (grad (fun i => x i + α * d i) - grad x) d
      ≤ L * α * (vnorm d)^2 := by
    exact
      (lipschitzUpperBound
        (grad := grad)
        (x := x) (d := d)
        (α := α) (L := L)
        (hα := hα)
        (hgradLip := hgradLip))
  exact le_trans h1 h2
lemma div_le_of_le_mul
  {a b c : ℝ}
  (hc : 0 < c)
  (h : a ≤ b * c) :
  a / c ≤ b := by
  have :=
    mul_le_mul_of_nonneg_right h (le_of_lt (inv_pos.mpr hc))
  have hcne : c ≠ 0 :=
    ne_of_gt hc
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hcne]
    using this
lemma alpha_lower_bound
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0)
  (hposd : vnorm d ≠ 0)
  (hw : wolfe f grad x d α c1 c2)
  (hgradLip : GradLipschitz grad L) :
  α ≥
    ((1 - c2) * (- innerpro (grad x) d))
      / (L * (vnorm d)^2) := by
  have hmain :=
    alpha_lower_bound_mul f grad x d α c1 c2 L hα hw hgradLip
  have hineq :
    (1 - c2) * (- innerpro (grad x) d)
      ≤ (L * (vnorm d)^2) * α := by
    linarith
  have hden_pos : 0 < L * (vnorm d)^2 := by
    have hpos : vnorm d > 0 :=
      lt_of_le_of_ne (vnorm_nonneg d) (by
        intro h
        apply hposd
        exact h.symm)
    have : 0 < (vnorm d)^2 :=
      pow_pos hpos 2
    exact mul_pos hL this
  have hineq' :
    (1 - c2) * (- innerpro (grad x) d)
      ≤ α * (L * (vnorm d)^2) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hineq
  have :=
    div_le_of_le_mul hden_pos hineq'
  exact this
lemma innerpro_neg_grad
  (grad : Vec n → Vec n)
  (x : Vec n) :
  innerpro (grad x) (-grad x)
    = - innerpro (grad x) (grad x) := by
  unfold innerpro
  have h1 :
    (∑ i, grad x i * (- grad x i))
      = ∑ i, - (grad x i)^2 := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have h2 :
    ∑ i, - (grad x i)^2
      = - ∑ i, (grad x i)^2 := by
    simp
  have hsq :
    innerpro (grad x) (grad x)
      = ∑ i, (grad x i)^2 := by
    unfold innerpro
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    ∑ i, grad x i * (- grad x i)
        = ∑ i, - (grad x i)^2 := h1
    _   = - ∑ i, (grad x i)^2 := h2
    _   = - innerpro (grad x) (grad x) := by
      simp [hsq]
lemma alpha_lower_bound_neg_grad
  (x : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hα : α ≥ 0)
  (hpos : vnorm (grad x) ≠ 0)
  (hw : wolfe f grad x (-grad x) α c1 c2)
  (hgradLip : GradLipschitz grad L) :
  α ≥ (1 - c2) / L :=
by
  have hmain :=
    alpha_lower_bound f grad x (-grad x) α c1 c2 L
      hL hα
      (by
        simpa [vnorm_neg] using hpos)
      hw hgradLip
  have hinner :
    innerpro (grad x) (-grad x)
      = - innerpro (grad x) (grad x) :=
    innerpro_neg_grad grad x
  have hmain' :
    α ≥ (1 - c2) * innerpro (grad x) (grad x) /
          (L * innerpro (grad x) (grad x)) :=
  by
    have heq :
      (1 - c2) * (- innerpro (grad x) (-grad x)) / (L * (vnorm (-grad x))^2)
        = (1 - c2) * innerpro (grad x) (grad x)
            / (L * innerpro (grad x) (grad x)) := by
      rw [hinner, vnorm_neg, vnorm_sq (grad x)]; ring
    rw [heq] at hmain
    exact hmain
  let A := innerpro (grad x) (grad x)
  have hApos : A ≠ 0 :=
  by
    intro h
    apply hpos
    have : (vnorm (grad x))^2 = 0 :=
    by
      rw [vnorm_sq (grad x)]; exact h
    have : vnorm (grad x) = 0 :=
      pow_eq_zero_iff (by norm_num) |>.mp this
    exact this
  have :
    α ≥ (1 - c2) * A / (L * A) :=
    hmain'
  have hL_ne : L ≠ 0 :=
    ne_of_gt hL
  have hfinal :
    (1 - c2) * A / (L * A)
      = (1 - c2) / L :=
  by
    field_simp [hApos, hL_ne]
    try ring
  simpa [hfinal] using this
noncomputable def cos_theta
  (grad : Vec n → Vec n)
  (x d : Vec n) : ℝ :=
  - innerpro (grad x) d /
    (vnorm (grad x) * vnorm d)
lemma cos_theta_nonneg
  (x d : Vec n)
  (hdesc : innerpro (grad x) d < 0)
  (hgrad_pos : 0 < vnorm (grad x))
  (hd_pos : 0 < vnorm d) :
  0 ≤ cos_theta grad x d :=
by
  unfold cos_theta
  have hnum : 0 < - innerpro (grad x) d :=
  by
    linarith
  have hden : 0 < vnorm (grad x) * vnorm d :=
    mul_pos hgrad_pos hd_pos
  exact div_nonneg hnum.le hden.le
lemma innerproCosThetaIdentity
  (x d : Vec n)
  (hgrad : vnorm (grad x) ≠ 0)
  (hd : vnorm d ≠ 0) :
  (innerpro (grad x) d)^2
    =
    (cos_theta grad x d)^2
      * (vnorm (grad x))^2
      * (vnorm d)^2 :=
by
  unfold cos_theta
  field_simp [hgrad, hd]
  try ring
lemma zoutendijkStepCore
  (x d : Vec n)
  (α c1 c2 L : ℝ)
  (hL : L > 0)
  (hwolfe : wolfe f grad x d α c1 c2)
  (hdesc : innerpro (grad x) d < 0)
  (hd : vnorm d ≠ 0)
  (hgrad : vnorm (grad x) ≠ 0)
  (hc1 : 0 < c1)
  (hα_pos : α > 0)
  (hgradLip : GradLipschitz grad L) :
  f x - f (fun i => x i + α * d i)
    ≥ c1 * (1 - c2) / L
        * (cos_theta grad x d)^2
        * (vnorm (grad x))^2 :=
by
  have h_armijo : armijo f grad x d α c1 :=
    wolfeImpliesArmijo f grad x d α c1 c2 hwolfe
  unfold armijo at h_armijo
  have h_decrease :
    f x - f (fun i => x i + α * d i)
      ≥ -c1 * α * innerpro (grad x) d :=
  by
    linarith
  have h_alpha_lower :
    α ≥
      (1 - c2) * (-innerpro (grad x) d)
        / (L * (vnorm d)^2) :=
    alpha_lower_bound f grad x d α c1 c2 L hL
      (le_of_lt hα_pos) hd hwolfe hgradLip
  have h_subst :
    -c1 * α * innerpro (grad x) d
      ≥ c1 * (1 - c2) / L
          * (innerpro (grad x) d)^2
          / (vnorm d)^2 :=
  by
    have h_neg :
      -innerpro (grad x) d > 0 :=
    by
      linarith
    have hnorm_pos :
      vnorm d > 0 :=
      lt_of_le_of_ne (vnorm_nonneg d) (Ne.symm hd)
    have h_denom_pos :
      L * (vnorm d)^2 > 0 :=
      mul_pos hL (pow_pos hnorm_pos 2)
    have h_denom_ne :
      L * (vnorm d)^2 ≠ 0 :=
      ne_of_gt h_denom_pos
    have h5 :
      c1 * α * (-innerpro (grad x) d)
        ≥ c1 *
            ((1 - c2) * (-innerpro (grad x) d)
              / (L * (vnorm d)^2))
            * (-innerpro (grad x) d) :=
    by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · exact h_alpha_lower
        · linarith
      · linarith
    have h6 :
      c1 *
          ((1 - c2) * (-innerpro (grad x) d)
            / (L * (vnorm d)^2))
          * (-innerpro (grad x) d)
        =
        c1 * (1 - c2) / L
          * (innerpro (grad x) d)^2
          / (vnorm d)^2 :=
    by
      field_simp [h_denom_ne]
      try ring
    have h_left :
      -c1 * α * innerpro (grad x) d
        = c1 * α * (-innerpro (grad x) d) :=
    by
      ring
    linarith [h_left, h5, h6]
  have h_cos :
    (innerpro (grad x) d)^2 / (vnorm d)^2
      =
    (cos_theta grad x d)^2
      * (vnorm (grad x))^2 :=
  by
    unfold cos_theta
    have h_grad_ne :
      vnorm (grad x) ≠ 0 :=
      hgrad
    have h_d_ne :
      vnorm d ≠ 0 :=
      hd
    field_simp [h_grad_ne, h_d_ne]
    try ring
  calc
    f x - f (fun i => x i + α * d i)
        ≥ -c1 * α * innerpro (grad x) d :=
      h_decrease
    _   ≥ c1 * (1 - c2) / L
            * (innerpro (grad x) d)^2
            / (vnorm d)^2 :=
      h_subst
    _   = c1 * (1 - c2) / L
            * ((innerpro (grad x) d)^2 / (vnorm d)^2) :=
      by ring
    _   = c1 * (1 - c2) / L
            * (cos_theta grad x d)^2
            * (vnorm (grad x))^2 :=
      by
        rw [h_cos]
        ring
lemma telescope_sum
  (x_seq : ℕ → Vec n) (k : ℕ) :
  ∑ i ∈ Finset.range k,
      (f (x_seq i) - f (x_seq (i + 1)))
    =
  f (x_seq 0) - f (x_seq k) :=
by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
theorem zoutendijkTheorem
  (c1 γ α0 L c2 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hgradLip : GradLipschitz grad L)
  (hbb : ∃ m : ℝ, ∀ x : Vec n, f x ≥ m)
  (hfo : FirstOrderApprox f grad)
  (hL : L > 0)
  (hc2 : 0 < c2 ∧ c2 < 1)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (hwolfe_all :
    ∀ k,
      wolfe f grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k))
        (btAlpha f grad
          (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k)
          (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k))
          c1 γ α0
          (hdesc_all _)
          hc1 hγ hα0 hfo)
        c1 c2)
  (hα_pos_all :
    ∀ k,
      btAlpha f grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k))
        c1 γ α0
        (hdesc_all _)
        hc1 hγ hα0 hfo > 0)
  (hgrad_ne_zero :
    ∀ k,
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k)) ≠ 0)
  (k : ℕ) :
  ∑ i ∈ Finset.range k,
      (cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)))^2
      *
      (vnorm (grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)))^2
    ≤
      L / (c1 * (1 - c2)) *
        (f x0 - Classical.choose hbb) :=
by
  classical
  set m := Classical.choose hbb
  have hm := Classical.choose_spec hbb
  let x_seq_vec : ℕ → Vec n :=
    fun i =>
      x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i
  have hx0 : x_seq_vec 0 = x0 :=
  by
    simp [x_seq_vec, x_seq]
  have h_step :
    ∀ i,
      f (x_seq_vec i) - f (x_seq_vec (i + 1))
      ≥
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (vnorm (grad (x_seq_vec i)))^2 :=
  by
    intro i
    let x_i := x_seq_vec i
    let d_i := -grad x_i
    let α_i :=
      btAlpha f grad x_i d_i c1 γ α0
        (hdesc_all x_i) hc1 hγ hα0 hfo
    have h_core :=
      zoutendijkStepCore
        (f := f) (grad := grad)
        (x := x_i) (d := d_i) (α := α_i)
        (c1 := c1) (c2 := c2) (L := L)
        (hL := hL)
        (hwolfe := hwolfe_all i)
        (hdesc := by simpa [d_i] using (hdesc_all x_i))
        (hd := by simpa [d_i, vnorm_neg] using (hgrad_ne_zero i))
        (hgrad := hgrad_ne_zero i)
        (hc1 := hc1.1)
        (hα_pos := hα_pos_all i)
        (hgradLip := hgradLip)
    have h_update :
      x_seq_vec (i + 1) = update x_i d_i α_i :=
    by
      simp [x_seq_vec, x_seq, next_x, x_i, d_i, α_i]
    have h_core' :
      f x_i - f (update x_i d_i α_i)
        ≥
          c1 * (1 - c2) / L *
            (cos_theta grad x_i d_i)^2 *
            (vnorm (grad x_i))^2 :=
    by
      simpa using h_core
    have h_step_i :
      f x_i - f (x_seq_vec (i + 1))
        ≥
          c1 * (1 - c2) / L *
            (cos_theta grad x_i d_i)^2 *
            (vnorm (grad x_i))^2 :=
    by
      simpa [h_update] using h_core'
    simpa [x_i, d_i] using h_step_i
  -- telescope
  have h_tel :=
    telescope_sum (f := f) (x_seq := x_seq_vec) (k := k)
  have h_sum :
    ∑ i ∈ Finset.range k,
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (vnorm (grad (x_seq_vec i)))^2
      ≤
    ∑ i ∈ Finset.range k,
        (f (x_seq_vec i) - f (x_seq_vec (i + 1))) :=
  by
    refine Finset.sum_le_sum ?_
    intro i hi
    simpa using (h_step i)
  have h_mid :
    ∑ i ∈ Finset.range k,
        c1 * (1 - c2) / L *
          (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
          (vnorm (grad (x_seq_vec i)))^2
      ≤
    f x0 - f (x_seq_vec k) :=
  by
    simpa [h_tel, hx0] using h_sum
  have h_bound :
    f x0 - f (x_seq_vec k) ≤ f x0 - m :=
  by
    have := hm (x_seq_vec k)
    linarith
  have h_total :=
    le_trans h_mid h_bound
  set S :=
    ∑ i ∈ Finset.range k,
      (cos_theta grad (x_seq_vec i) (-grad (x_seq_vec i)))^2 *
      (vnorm (grad (x_seq_vec i)))^2
  have h_scaled :
    (c1 * (1 - c2) / L) * S ≤ f x0 - m :=
  by
    simpa
      [S, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      using h_total
  have h_pos_mul :
    0 < c1 * (1 - c2) :=
    mul_pos hc1.1 (sub_pos.mpr hc2.2)
  have h_pos :
    0 < c1 * (1 - c2) / L :=
    div_pos h_pos_mul hL
  have h_inv_pos :
    0 < L / (c1 * (1 - c2)) :=
    div_pos hL h_pos_mul
  have h_mul :=
    mul_le_mul_of_nonneg_left
      h_scaled
      (le_of_lt h_inv_pos)
  have h_cancel :
    (L / (c1 * (1 - c2))) *
      (c1 * (1 - c2) / L) = 1 :=
  by
    rw [div_mul_div_comm, mul_comm L (c1 * (1 - c2)),
      div_self (mul_ne_zero (ne_of_gt h_pos_mul) (ne_of_gt hL))]
  have h_final :
    S ≤ (f x0 - m) * (L / (c1 * (1 - c2))) :=
  by
    have h₁ :
      (L / (c1 * (1 - c2))) *
          (c1 * (1 - c2) / L * S)
        =
      ((L / (c1 * (1 - c2))) *
          (c1 * (1 - c2) / L)) * S :=
    by
      ring
    have h₂ :
      ((L / (c1 * (1 - c2))) *
        (c1 * (1 - c2) / L)) = 1 :=
      h_cancel
    have h₃ :
      S ≤ (L / (c1 * (1 - c2))) *
            (f x0 - m) :=
    by
      simpa [h₁, h₂] using h_mul
    simpa [mul_comm] using h₃
  simpa [S, m, mul_comm] using h_final

lemma subseq_sum_le_full_sum
  {n : ℕ}
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x0 : Vec n)
  (c1 γ α0 : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (hfo : FirstOrderApprox f grad)
  (φ : ℕ → ℕ)
  (hmono : StrictMono φ)
  (K : ℕ) :
  ∑ i ∈ Finset.range K,
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ i))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ i))) ^ 2 *
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ i))) ^ 2
  ≤
  ∑ i ∈ Finset.range (φ K),
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 *
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 := by
  have h_image_subset : Finset.image φ (Finset.range K) ⊆ Finset.range (φ K) := by
    exact Finset.image_subset_iff.mpr fun i hi => Finset.mem_range.mpr ( hmono ( Finset.mem_range.mp hi ) );
  convert Finset.sum_le_sum_of_subset_of_nonneg h_image_subset _ using 1;
  · rw [ Finset.sum_image <| by intros a ha b hb hab; exact hmono.injective hab ];
  · infer_instance;
  · exact fun _ _ _ => mul_nonneg ( sq_nonneg _ ) ( sq_nonneg _ )
theorem globalConvergenceCore
  (n : ℕ)
  (f : Vec n → ℝ)
  (grad : Vec n → Vec n)
  (x0 : Vec n)
  (c1 γ α0 L : ℝ)
  (hc1 : 0 < c1 ∧ c1 < 1)
  (hγ : 0 < γ ∧ γ < 1)
  (hα0 : α0 > 0)
  (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
  (hfo : FirstOrderApprox f grad)
  -- Zoutendijk bound
  (hZ :
    ∀ k,
      ∑ i ∈ Finset.range k,
        cos_theta grad
          (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)
          (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 *
        vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2
      ≤ L)
  (ε : ℝ)
  (hε : ε > 0)
  (φ : ℕ → ℕ)
  (hmono : StrictMono φ)
  (hlower :
    ∀ k,
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))) ^ 2 ≥ ε ^ 2)
  (hcos :
    ∀ k,
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))) ^ 2 = 1)
  :
  False := by
  let a : ℕ → ℝ :=
    fun k =>
      cos_theta grad
        (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))
        (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))) ^ 2 *
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo (φ k))) ^ 2
  have hterm : ∀ k, a k ≥ ε ^ 2 := by
    intro k
    have h1 := hcos k
    have h2 := hlower k
    simp [a, h1]
    exact h2
  have hsum_lower :
    ∀ K,
      ∑ i ∈ Finset.range K, a i ≥ (K : ℝ) * ε ^ 2 := by
    intro K
    induction K with
    | zero =>
        simp
    | succ K ih =>
        have hK := hterm K
        have hsum :=
          Finset.sum_range_succ (fun i => a i) K
        simp [hsum]
        have : (∑ i ∈ Finset.range K, a i) + a K
              ≥ (K : ℝ) * ε ^ 2 + ε ^ 2 := by
          exact add_le_add ih hK
        have hrewrite :
          (K : ℝ) * ε ^ 2 + ε ^ 2 = (K + 1 : ℝ) * ε ^ 2 := by
          ring
        simpa [hrewrite]
  have hbounded :
    ∀ K,
      ∑ i ∈ Finset.range K, a i ≤ L := by
    intro K
    have := hZ (φ K)
    have hsubset :
      ∑ i ∈ Finset.range K, a i
      ≤ ∑ i ∈ Finset.range (φ K),
          cos_theta grad
            (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)
            (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 *
          vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 := by
      simpa [a] using
        subseq_sum_le_full_sum
          f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo φ hmono K
    exact le_trans hsubset this
  have hpos : ε ^ 2 > 0 := by
    have := hε
    nlinarith
  let K : ℕ := Nat.succ (Nat.ceil (L / (ε ^ 2)))
  have hK_ge :
    (K : ℝ) ≥ L / (ε ^ 2) + 1 := by
    have hceil : (Nat.ceil (L / (ε ^ 2)) : ℝ) ≥ L / (ε ^ 2) :=
      Nat.le_ceil _
    have : (K : ℝ) = (Nat.ceil (L / (ε ^ 2)) : ℝ) + 1 := by
      simp [K]
    linarith
  have hmul :
    (K : ℝ) * ε ^ 2 ≥ (L / (ε ^ 2) + 1) * ε ^ 2 :=
    mul_le_mul_of_nonneg_right hK_ge (by positivity)
  have hrewrite :
    (L / (ε ^ 2) + 1) * ε ^ 2 = L + ε ^ 2 := by
    field_simp [hpos.ne']
  have hbig :
    (K : ℝ) * ε ^ 2 ≥ L + ε ^ 2 := by
    simpa [hrewrite] using hmul
  have hupper := hbounded K
  have hlower' := hsum_lower K
  have hle :
    (K : ℝ) * ε ^ 2 ≤ L := by
    exact le_trans hlower' hupper
  have : (K : ℝ) * ε ^ 2 < L + ε ^ 2 := by
    linarith
  exact lt_irrefl _ (lt_of_le_of_lt hbig this)

lemma cos_theta_neg_grad_eq_one
    (x : Vec n) (hgx : vnorm (grad x) ≠ 0) :
    cos_theta grad x (-grad x) = 1 := by
  unfold cos_theta
  rw [innerpro_neg_grad grad x, vnorm_neg, ← vnorm_sq (grad x)]
  have hne : (vnorm (grad x))^2 ≠ 0 := pow_ne_zero _ hgx
  field_simp
  try ring

lemma cos_theta_neg_grad_sq_eq_one
    (x : Vec n) (hgx : vnorm (grad x) ≠ 0) :
    (cos_theta grad x (-grad x))^2 = 1 := by
  rw [cos_theta_neg_grad_eq_one grad x hgx]; norm_num

lemma gradient_norm_inf_zero
    (xs : ℕ → Vec n) (L : ℝ)
    (hZ : ∀ k,
      ∑ i ∈ Finset.range k,
        cos_theta grad (xs i) (-grad (xs i)) ^ 2 *
        vnorm (grad (xs i)) ^ 2 ≤ L) :
    ∀ ε > 0, ∃ k, vnorm (grad (xs k)) < ε := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ k, ε ≤ vnorm (grad (xs k))`
  have hpos : (0 : ℝ) < ε ^ 2 := by positivity
  have hterm : ∀ i,
      ε ^ 2 ≤ cos_theta grad (xs i) (-grad (xs i)) ^ 2 * vnorm (grad (xs i)) ^ 2 := by
    intro i
    have hge : ε ≤ vnorm (grad (xs i)) := hcon i
    have hne : vnorm (grad (xs i)) ≠ 0 := by
      intro h; rw [h] at hge; linarith
    rw [cos_theta_neg_grad_sq_eq_one grad (xs i) hne, one_mul]
    nlinarith [hge, hε.le, vnorm_nonneg (grad (xs i))]
  have hsum : ∀ k : ℕ,
      (k : ℝ) * ε ^ 2 ≤
        ∑ i ∈ Finset.range k,
          cos_theta grad (xs i) (-grad (xs i)) ^ 2 *
          vnorm (grad (xs i)) ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, Nat.cast_succ, add_mul, one_mul]
        exact add_le_add ih (hterm k)
  obtain ⟨k, hk⟩ := exists_nat_gt (L / ε ^ 2)
  have hkbound : (k : ℝ) * ε ^ 2 ≤ L := le_trans (hsum k) (hZ k)
  have : (k : ℝ) ≤ L / ε ^ 2 := by rw [le_div_iff₀ hpos]; linarith
  linarith [hk]

theorem globalConvergence
    (c1 γ α0 L : ℝ)
    (hc1 : 0 < c1 ∧ c1 < 1)
    (hγ : 0 < γ ∧ γ < 1)
    (hα0 : α0 > 0)
    (hdesc_all : ∀ x, isDescentDirection grad x (-grad x))
    (hfo : FirstOrderApprox f grad)
    (hZ : ∀ k,
      ∑ i ∈ Finset.range k,
        cos_theta grad
          (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)
          (-grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 *
        vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i)) ^ 2 ≤ L) :
    ∀ ε > 0, ∃ k,
      vnorm (grad (x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo k)) < ε :=
  gradient_norm_inf_zero grad
    (fun i => x_seq f grad x0 c1 γ α0 hc1 hγ hα0 hdesc_all hfo i) L hZ

section Satisfiability
variable {m : ℕ}

lemma innerpro_linear_step (b x d : Vec m) (α : ℝ) :
    innerpro b (fun i => x i + α * d i)
      = innerpro b x + α * innerpro b d := by
  unfold innerpro
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (by intro i _; ring)

lemma gradLipschitz_const (b : Vec m) (L : ℝ) (hL : 0 ≤ L) :
    GradLipschitz (fun _ => b) L := by
  intro x y
  have hz : ((fun _ => b) x - (fun _ => b) y)
      = (fun _ : Fin m => (0 : ℝ)) := by
    funext i; simp
  have hv : vnorm ((fun _ => b) x - (fun _ => b) y) = 0 := by
    rw [hz]; unfold vnorm innerpro; simp
  rw [hv]
  exact mul_nonneg hL (vnorm_nonneg _)

lemma firstOrderApprox_linear (b : Vec m) :
    FirstOrderApprox (fun x => innerpro b x) (fun _ => b) := by
  intro x d c1 hc1 hc1' hdesc
  refine ⟨1, one_pos, ?_⟩
  intro α hα
  have hαpos : 0 < α := hα.1
  simp only []
  rw [innerpro_linear_step]
  -- goal: ⟨b,x⟩ + α⟨b,d⟩ ≤ ⟨b,x⟩ + c1·α·⟨b,d⟩
  have hbd : innerpro b d < 0 := hdesc
  nlinarith [mul_pos hαpos (neg_pos.mpr hbd), hc1, hc1']

theorem modelling_hypotheses_satisfiable (b : Vec m) (L : ℝ) (hL : 0 ≤ L) :
    GradLipschitz (fun _ => b) L
      ∧ FirstOrderApprox (fun x => innerpro b x) (fun _ => b) :=
  ⟨gradLipschitz_const b L hL, firstOrderApprox_linear b⟩
end Satisfiability
