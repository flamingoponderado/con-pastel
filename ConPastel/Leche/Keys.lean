import ConLeche.Frontend.Scan.Equiv.Keys
import ConPastel.Leche.Datatypes

/-!
# The frontend's key lookup, by first byte

`keyOf` searches `keyTable`, a constant list of 65 spellings. A constant is
a thunk in the translation, so every key read rebuilt the table and the
byte lists of its spellings. `keyOfF` dispatches on the first byte, then
compares the rest with the few spellings left (con-leche's `keyOf_97` …).
-/

namespace ConPastel.Impl
open ConLeche ConLeche.Frontend

/-- `keyOf`, by first byte. -/
def keyOfF : List UInt8 → Key
  | [] => .kUnknown
  | c :: k' =>
    if c = 97 then
      if k' = [108, 108] then Key.kAll
      else if k' = [112, 112] then Key.kApp
      else if k' = [114, 103] then Key.kArg
      else if k' = [120, 105, 111, 109] then Key.kAxiom
      else Key.kUnknown
    else if c = 98 then
      if k' = [105, 110, 100, 101, 114, 73, 110, 102, 111] then Key.kBinderInfo
      else if k' = [111, 100, 121] then Key.kBody
      else if k' = [118, 97, 114] then Key.kBvar
      else Key.kUnknown
    else if c = 99 then
      if k' = [105, 100, 120] then Key.kCidx
      else if k' = [111, 110, 115, 116] then Key.kConst
      else if k' = [116, 111, 114] then Key.kCtor
      else if k' = [116, 111, 114, 115] then Key.kCtors
      else Key.kUnknown
    else if c = 100 then
      if k' = [101, 102] then Key.kDef
      else Key.kUnknown
    else if c = 102 then
      if k' = [110] then Key.kFn
      else if k' = [111, 114, 97, 108, 108, 69] then Key.kForallE
      else Key.kUnknown
    else if c = 104 then
      if k' = [105, 110, 116, 115] then Key.kHints
      else Key.kUnknown
    else if c = 105 then
      if k' = [] then Key.kI
      else if k' = [100, 120] then Key.kIdx
      else if k' = [101] then Key.kIe
      else if k' = [108] then Key.kIl
      else if k' = [109, 97, 120] then Key.kImax
      else if k' = [110] then Key.kIn
      else if k' = [110, 100, 117, 99, 116] then Key.kInduct
      else if k' = [110, 100, 117, 99, 116, 105, 118, 101] then Key.kInductive
      else if k' = [115, 82, 101, 99] then Key.kIsRec
      else if k' = [115, 82, 101, 102, 108, 101, 120, 105, 118, 101] then Key.kIsReflexive
      else if k' = [115, 85, 110, 115, 97, 102, 101] then Key.kIsUnsafe
      else Key.kUnknown
    else if c = 107 then
      if k' = [] then Key.kK
      else if k' = [105, 110, 100] then Key.kKind
      else Key.kUnknown
    else if c = 108 then
      if k' = [97, 109] then Key.kLam
      else if k' = [101, 116, 69] then Key.kLetE
      else if k' = [101, 118, 101, 108, 80, 97, 114, 97, 109, 115] then Key.kLevelParams
      else Key.kUnknown
    else if c = 109 then
      if k' = [97, 120] then Key.kMax
      else if k' = [101, 116, 97] then Key.kMeta
      else Key.kUnknown
    else if c = 110 then
      if k' = [97, 109, 101] then Key.kName
      else if k' = [97, 116, 86, 97, 108] then Key.kNatVal
      else if k' = [102, 105, 101, 108, 100, 115] then Key.kNfields
      else if k' = [111, 110, 100, 101, 112] then Key.kNondep
      else if k' = [117, 109] then Key.kNum
      else if k' = [117, 109, 70, 105, 101, 108, 100, 115] then Key.kNumFields
      else if k' = [117, 109, 73, 110, 100, 105, 99, 101, 115] then Key.kNumIndices
      else if k' = [117, 109, 77, 105, 110, 111, 114, 115] then Key.kNumMinors
      else if k' = [117, 109, 77, 111, 116, 105, 118, 101, 115] then Key.kNumMotives
      else if k' = [117, 109, 78, 101, 115, 116, 101, 100] then Key.kNumNested
      else if k' = [117, 109, 80, 97, 114, 97, 109, 115] then Key.kNumParams
      else Key.kUnknown
    else if c = 111 then
      if k' = [112, 97, 113, 117, 101] then Key.kOpaque
      else Key.kUnknown
    else if c = 112 then
      if k' = [97, 114, 97, 109] then Key.kParam
      else if k' = [114, 101] then Key.kPre
      else if k' = [114, 111, 106] then Key.kProj
      else Key.kUnknown
    else if c = 113 then
      if k' = [117, 111, 116] then Key.kQuot
      else Key.kUnknown
    else if c = 114 then
      if k' = [101, 99, 115] then Key.kRecs
      else if k' = [101, 103, 117, 108, 97, 114] then Key.kRegular
      else if k' = [104, 115] then Key.kRhs
      else if k' = [117, 108, 101, 115] then Key.kRules
      else Key.kUnknown
    else if c = 115 then
      if k' = [97, 102, 101, 116, 121] then Key.kSafety
      else if k' = [111, 114, 116] then Key.kSort
      else if k' = [116, 114] then Key.kStr
      else if k' = [116, 114, 86, 97, 108] then Key.kStrVal
      else if k' = [116, 114, 117, 99, 116] then Key.kStruct
      else if k' = [117, 99, 99] then Key.kSucc
      else Key.kUnknown
    else if c = 116 then
      if k' = [104, 109] then Key.kThm
      else if k' = [121, 112, 101] then Key.kType
      else if k' = [121, 112, 101, 78, 97, 109, 101] then Key.kTypeName
      else if k' = [121, 112, 101, 115] then Key.kTypes
      else Key.kUnknown
    else if c = 117 then
      if k' = [115] then Key.kUs
      else Key.kUnknown
    else if c = 118 then
      if k' = [97, 108, 117, 101] then Key.kValue
      else Key.kUnknown
    else .kUnknown

set_option linter.deprecated false in
set_option maxRecDepth 200000 in
theorem keyOf_eq_F (k : List UInt8) : keyOf k = keyOfF k := by
  cases k with
  | nil => exact keyOf_nil
  | cons c k' =>
    simp only [keyOfF]
    by_cases e97 : c = 97
    · subst e97; rw [keyOf_97]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e97)]
    by_cases e98 : c = 98
    · subst e98; rw [keyOf_98]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e98)]
    by_cases e99 : c = 99
    · subst e99; rw [keyOf_99]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e99)]
    by_cases e100 : c = 100
    · subst e100; rw [keyOf_100]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e100)]
    by_cases e102 : c = 102
    · subst e102; rw [keyOf_102]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e102)]
    by_cases e104 : c = 104
    · subst e104; rw [keyOf_104]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e104)]
    by_cases e105 : c = 105
    · subst e105; rw [keyOf_105]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e105)]
    by_cases e107 : c = 107
    · subst e107; rw [keyOf_107]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e107)]
    by_cases e108 : c = 108
    · subst e108; rw [keyOf_108]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e108)]
    by_cases e109 : c = 109
    · subst e109; rw [keyOf_109]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e109)]
    by_cases e110 : c = 110
    · subst e110; rw [keyOf_110]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e110)]
    by_cases e111 : c = 111
    · subst e111; rw [keyOf_111]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e111)]
    by_cases e112 : c = 112
    · subst e112; rw [keyOf_112]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e112)]
    by_cases e113 : c = 113
    · subst e113; rw [keyOf_113]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e113)]
    by_cases e114 : c = 114
    · subst e114; rw [keyOf_114]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e114)]
    by_cases e115 : c = 115
    · subst e115; rw [keyOf_115]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e115)]
    by_cases e116 : c = 116
    · subst e116; rw [keyOf_116]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e116)]
    by_cases e117 : c = 117
    · subst e117; rw [keyOf_117]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e117)]
    by_cases e118 : c = 118
    · subst e118; rw [keyOf_118]; rfl
    rw [ite_cond_eq_false _ _ (eq_false e118)]
    have f97 : ((97 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e97 hx.symm
    have f98 : ((98 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e98 hx.symm
    have f99 : ((99 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e99 hx.symm
    have f100 : ((100 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e100 hx.symm
    have f102 : ((102 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e102 hx.symm
    have f104 : ((104 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e104 hx.symm
    have f105 : ((105 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e105 hx.symm
    have f107 : ((107 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e107 hx.symm
    have f108 : ((108 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e108 hx.symm
    have f109 : ((109 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e109 hx.symm
    have f110 : ((110 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e110 hx.symm
    have f111 : ((111 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e111 hx.symm
    have f112 : ((112 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e112 hx.symm
    have f113 : ((113 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e113 hx.symm
    have f114 : ((114 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e114 hx.symm
    have f115 : ((115 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e115 hx.symm
    have f116 : ((116 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e116 hx.symm
    have f117 : ((117 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e117 hx.symm
    have f118 : ((118 : UInt8) == c) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact fun hx => e118 hx.symm
    unfold keyOf keyTable
    simp only [List.find?_cons, lit_all, lit_app, lit_arg, lit_axiom, lit_binderInfo,
    lit_body, lit_bvar, lit_cidx, lit_const, lit_ctor, lit_ctors, lit_def, lit_fn,
    lit_forallE, lit_hints, lit_i, lit_idx, lit_ie, lit_il, lit_imax, lit_in, lit_induct,
    lit_inductive, lit_isRec, lit_isReflexive, lit_isUnsafe, lit_k, lit_kind, lit_lam,
    lit_letE, lit_levelParams, lit_max, lit_meta, lit_name, lit_natVal, lit_nfields,
    lit_nondep, lit_num, lit_numFields, lit_numIndices, lit_numMinors, lit_numMotives,
    lit_numNested, lit_numParams, lit_opaque, lit_param, lit_pre, lit_proj,
    lit_quot, lit_recs, lit_regular, lit_rhs, lit_rules, lit_safety, lit_sort, lit_str,
    lit_strVal, lit_struct, lit_succ, lit_thm, lit_type, lit_typeName, lit_types, lit_us,
    lit_value]
    simp [f97, f98, f99, f100, f102, f104, f105, f107, f108, f109, f110, f111, f112, f113, f114, f115, f116, f117, f118]

end ConPastel.Impl

cake_replace ConLeche.Frontend.keyOf ConPastel.Impl.keyOfF ConPastel.Impl.keyOf_eq_F
