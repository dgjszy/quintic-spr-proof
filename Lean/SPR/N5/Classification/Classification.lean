import Mathlib

/-!
Exhaustive finite sign classification in the Lean kernel.
Its analytic inputs (root bands, contact phases, and interpolation signs) are
not asserted here. No Python certificate or native_decide is used.

## 与论文的对应

论文 §5 与附录 A：必要候选表的完备性及基本排除。
完整枚举满足符号与区域路径约束的必要候选；不宣称每个候选可实现。
-/
namespace SPR.N5.Direct.Classification

/-! ## 分母区域与路径判定 -/

/-- Signs 0,1,2,3 mean ++,-+,--,+-. Only nonzero contact components enter this table. -/
def zones : ℕ → List ℕ
  | 0 => [0, 1, 7, 8]
  | 1 => [1, 2, 3]
  | 2 => [3, 4, 5]
  | 3 => [5, 6, 7]
  | _ => []

/-- Declarative existence of a nondecreasing admissible region path. -/
inductive ZonePath : ℕ → List ℕ → Prop
  | nil (lo : ℕ) : ZonePath lo []
  | cons {lo s : ℕ} {ss : List ℕ} (z : ℕ)
      (hz : z ∈ zones s) (hlo : lo ≤ z) (hrest : ZonePath z ss) : ZonePath lo (s :: ss)

/-- 有限判定器：搜索不减的分母区域路径；与 ZonePath 的等价性在下方证明。 -/
def pathB (lo : ℕ) : List ℕ → Bool
  | [] => true
  | s :: ss => (zones s).any fun z => decide (lo ≤ z) && pathB z ss

theorem pathB_iff (lo : ℕ) (ss : List ℕ) : pathB lo ss = true ↔ ZonePath lo ss := by
  induction ss generalizing lo with
  | nil => simp [pathB, ZonePath.nil]
  | cons s ss ih =>
    simp only [pathB, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨z, hz, hlo, hp⟩
      exact .cons z hz hlo hp
    · intro h
      cases h with
      | cons z hz hlo hp => exact ⟨z, hz, hlo, hp⟩

/-! ## 分子区间编号的枚举 -/

/-- Nondecreasing words with all stages in [lo,hi). -/
def OrderedWord (lo hi : ℕ) : List ℕ → Prop
  | [] => True
  | s :: ss => lo ≤ s ∧ s < hi ∧ OrderedWord s hi ss

/-- 枚举长度固定且在 [lo,hi) 内不减的分子区间编号列表。 -/
def words (lo hi : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => ((List.range hi).filter fun s => decide (lo ≤ s)).flatMap
      fun s => (words s hi n).map (List.cons s)

theorem mem_words_iff (lo hi n : ℕ) (w : List ℕ) :
    w ∈ words lo hi n ↔ w.length = n ∧ OrderedWord lo hi w := by
  induction n generalizing lo w with
  | zero => cases w <;> simp [words, OrderedWord]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons s ss =>
      simp [words, List.mem_flatMap, ih, OrderedWord, and_assoc, and_left_comm, and_comm]

/-! ## 由插值符号得到候选 -/

/-- Numerator signs rotated from (E,O) to (O,-E). -/
def rotated : ℕ → ℕ
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | _ => 3

def signsFrom (flip : Bool) : List ℕ → List ℕ
  | [] => []
  | s :: ss => (if flip then (rotated s + 2) % 4 else rotated s) :: signsFrom (!flip) ss

/-- Sign of c eta_0: eta_0 has sign (-1)^(n-1); neg means c<0. -/
def initialFlip (n : ℕ) (neg : Bool) : Bool := ((n - 1) % 2 == 1) != neg

/-- 给定倍数符号及是否含零节点，计算按节点次序排列的分母符号编码。 -/
def contactSigns (n : ℕ) (neg origin : Bool) (w : List ℕ) : List ℕ :=
  if origin then 0 :: signsFrom (!(initialFlip n neg)) w else signsFrom (initialFlip n neg) w

/-- 用区域相容性筛选必要候选，不要求这些列表均可由实际接触实现。 -/
def admissibleWords (hi n : ℕ) (neg origin : Bool) : List (List ℕ) :=
  if origin && initialFlip n neg then [] else
    (words (if origin then 1 else 0) hi (n - if origin then 1 else 0)).filter
      fun w => pathB 0 (contactSigns n neg origin w)

/-- Exact assumptions consumed by the finite computation, with a declarative region path. -/
def Candidate (hi n : ℕ) (neg origin : Bool) (w : List ℕ) : Prop :=
  (origin && initialFlip n neg) = false ∧
  w.length = n - (if origin then 1 else 0) ∧
  OrderedWord (if origin then 1 else 0) hi w ∧
  ZonePath 0 (contactSigns n neg origin w)

theorem mem_admissibleWords_iff (hi n : ℕ) (neg origin : Bool) (w : List ℕ) :
    w ∈ admissibleWords hi n neg origin ↔ Candidate hi n neg origin w := by
  unfold admissibleWords Candidate
  split <;> simp_all [List.mem_filter, mem_words_iff, pathB_iff, and_assoc]

/-! ## 三张完整候选表 -/

/-- 候选行依次记录 c<0、零节点是否入选，以及正节点的分子区间编号。 -/
abbrev Row := Bool × Bool × List ℕ

def rows (hi n : ℕ) (signs : List Bool) : List Row :=
  signs.flatMap fun neg => [false, true].flatMap fun origin =>
    (admissibleWords hi n neg origin).map fun w => (neg, origin, w)

/-- 附录 A：五个有限节点及无穷远质量的两项候选。 -/
def infinityTable : List Row :=
  [(false, false, [1,1,2,2,3]), (false, true, [1,2,2,3])]

/-- 附录 A：六个有限节点且分子四次的三项候选。 -/
def quarticTable : List Row :=
  [(false, false, [0,1,1,2,2,3]), (true, false, [1,1,2,2,3,3]),
    (true, true, [1,2,2,3,3])]

/-- 附录 A：六个有限节点且分子五次的二十一项候选。 -/
def quinticTable : List Row :=
  [(false,false,[0,0,1,1,2,4]), (false,false,[0,0,1,1,3,4]),
   (false,false,[0,0,1,3,3,4]), (false,false,[0,0,2,3,3,4]),
   (false,false,[0,1,1,1,2,4]), (false,false,[0,1,1,1,3,4]),
   (false,false,[0,1,1,2,2,3]), (false,false,[0,1,1,2,2,4]),
   (false,false,[0,1,1,2,3,4]), (false,false,[0,1,1,2,4,4]),
   (false,false,[0,1,1,3,3,4]), (false,false,[0,1,1,3,4,4]),
   (false,false,[0,1,2,3,3,4]), (false,false,[0,1,3,3,3,4]),
   (false,false,[0,1,3,3,4,4]), (false,false,[0,2,2,3,3,4]),
   (false,false,[0,2,3,3,3,4]), (false,false,[0,2,3,3,4,4]),
   (false,false,[1,2,2,3,3,4]), (true,false,[1,1,2,2,3,3]),
   (true,true,[1,2,2,3,3])]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The complete finite table is reduced by the kernel, without an external certificate.
theorem infinity_table_exact : rows 4 5 [false] = infinityTable := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The complete finite table is reduced by the kernel, without an external certificate.
theorem quartic_table_exact : rows 4 6 [false, true] = quarticTable := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- The complete finite table is reduced by the kernel, without an external certificate.
theorem quintic_table_exact : rows 5 6 [false, true] = quinticTable := by decide +kernel

theorem mem_rows_iff (hi n : ℕ) (signs : List Bool) (neg origin : Bool) (w : List ℕ) :
    (neg, origin, w) ∈ rows hi n signs ↔ neg ∈ signs ∧ Candidate hi n neg origin w := by
  cases neg <;> cases origin <;> simp [rows, List.mem_flatMap, mem_admissibleWords_iff]

theorem quintic_classification {neg origin : Bool} {w : List ℕ}
    (h : Candidate 5 6 neg origin w) : (neg, origin, w) ∈ quinticTable := by
  rw [← quintic_table_exact, mem_rows_iff]
  exact ⟨by cases neg <;> simp, h⟩

theorem quartic_classification {neg origin : Bool} {w : List ℕ}
    (h : Candidate 4 6 neg origin w) : (neg, origin, w) ∈ quarticTable := by
  rw [← quartic_table_exact, mem_rows_iff]
  exact ⟨by cases neg <;> simp, h⟩

theorem infinity_classification {origin : Bool} {w : List ℕ}
    (h : Candidate 4 5 false origin w) : (false, origin, w) ∈ infinityTable := by
  rw [← infinity_table_exact, mem_rows_iff]
  exact ⟨by simp, h⟩

/-! ## 基本排除标签与五项剩余表 -/

/-- A and B are stages 1 and 2; D pools stages 0 and 4. -/
def cornerIndex (s : ℕ) : ℕ := if s = 4 then 0 else s

/-- Tags for the elementary analytic exclusions. This does not assert those
exclusions follow from Candidate alone. -/
def basicExcluded (hi : ℕ) (origin : Bool) (w : List ℕ) : Bool :=
  ((List.range 4).any fun c => decide (2 < (w.map cornerIndex).count c)) ||
  (hi == 4 && origin && ((List.range 4).any fun c => decide (2 ≤ (w.map cornerIndex).count c))) ||
  (decide (2 ≤ w.count 1) && decide (2 ≤ w.count 2)) ||
  (hi == 5 && origin && decide (2 ≤ w.count 2) && decide (2 ≤ w.count 3))

def surviving (hi n : ℕ) (signs : List Bool) : List Row :=
  (rows hi n signs).filter fun r => !(basicExcluded hi r.2.1 r.2.2)

/-- 论文表 2 的 Q1、Q2、Q3、Q4、Q5，顺序与论文一致。 -/
def finalFive : List Row :=
  [(false,false,[0,1,1,2,3,4]), (false,false,[0,1,1,3,3,4]),
   (false,false,[0,1,2,3,3,4]), (false,false,[0,2,2,3,3,4]),
   (false,false,[1,2,2,3,3,4])]

/-- The five retained interval sequences, in the Q1–Q5 order of paper Table 2.
This only decodes membership in the finite list; it does not assert realizability. -/
theorem finalFive_cases {q : Fin 6 → ℕ}
    (hrow : (false, false, List.ofFn q) ∈ finalFive) :
    q = ![0, 1, 1, 2, 3, 4] ∨ q = ![0, 1, 1, 3, 3, 4] ∨
    q = ![0, 1, 2, 3, 3, 4] ∨ q = ![0, 2, 2, 3, 3, 4] ∨
    q = ![1, 2, 2, 3, 3, 4] := by
  simp only [finalFive, List.mem_cons, List.not_mem_nil,
    Prod.mk.injEq, true_and, or_false] at hrow
  rcases hrow with hQ1 | hQ2 | hQ3 | hQ4 | hQ5
  · exact Or.inl (List.ofFn_injective (by simpa using hQ1))
  · exact Or.inr (Or.inl (List.ofFn_injective (by simpa using hQ2)))
  · exact Or.inr (Or.inr (Or.inl (List.ofFn_injective (by simpa using hQ3))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (List.ofFn_injective (by simpa using hQ4)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (List.ofFn_injective (by simpa using hQ5)))))

theorem infinity_no_survivor : surviving 4 5 [false] = [] := by
  rw [surviving, infinity_table_exact]
  decide

theorem quartic_no_survivor : surviving 4 6 [false, true] = [] := by
  rw [surviving, quartic_table_exact]
  decide

theorem quintic_five_survivors : surviving 5 6 [false, true] = finalFive := by
  rw [surviving, quintic_table_exact]
  decide

theorem remaining_quintic_mem_finalFive {neg origin : Bool} {w : List ℕ}
    (h : Candidate 5 6 neg origin w) (hnot : basicExcluded 5 origin w = false) :
    (neg, origin, w) ∈ finalFive := by
  rw [← quintic_five_survivors, surviving, List.mem_filter]
  exact ⟨(mem_rows_iff _ _ _ _ _ _).mpr ⟨by cases neg <;> simp, h⟩, by simpa using hnot⟩

/-- A zero numerator constant without zero-frequency support starts at stage 1.
The two surviving sign-compatible words both carry elementary exclusion tags. -/
theorem origin_zero_positive_support_tags :
    ((rows 5 6 [false, true]).filter fun r =>
      !r.2.1 && (r.2.2.all fun s => decide (1 ≤ s))).all
      (fun r => basicExcluded 5 true r.2.2) = true := by
  rw [quintic_table_exact]
  decide

end SPR.N5.Direct.Classification
