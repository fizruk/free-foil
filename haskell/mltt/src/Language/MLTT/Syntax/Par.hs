{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListModule
  , pModule
  , pParam
  , pListParam
  , pImport
  , pListImport
  , pDecl
  , pListDecl
  , pDischarge
  , pListVarIdent
  , pTerm
  , pTerm1
  , pTerm2
  , pScopedTerm
  , pPattern
  ) where

import Prelude

import qualified Language.MLTT.Syntax.Abs
import Language.MLTT.Syntax.Lex
import qualified Data.Array as Happy_Data_Array
import qualified Data.Bits as Bits
import Control.Applicative(Applicative(..))
import Control.Monad (ap)

-- parser produced by Happy Version 1.20.1.1

data HappyAbsSyn 
	= HappyTerminal (Token)
	| HappyErrorToken Prelude.Int
	| HappyAbsSyn19 ((Language.MLTT.Syntax.Abs.BNFC'Position, Integer))
	| HappyAbsSyn20 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn21 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn22 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Module]))
	| HappyAbsSyn23 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn24 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Param))
	| HappyAbsSyn25 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Param]))
	| HappyAbsSyn26 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn28 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn29 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn30 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Discharge))
	| HappyAbsSyn31 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.VarIdent]))
	| HappyAbsSyn32 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn35 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn36 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

{- to allow type-synonyms as our monads (likely
 - with explicitly-specified bind and return)
 - in Haskell98, it seems that with
 - /type M a = .../, then /(HappyReduction M)/
 - is not allowed.  But Happy is a
 - code-generator that can just substitute it.
type HappyReduction m = 
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> m HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> m HappyAbsSyn
-}

action_0,
 action_1,
 action_2,
 action_3,
 action_4,
 action_5,
 action_6,
 action_7,
 action_8,
 action_9,
 action_10,
 action_11,
 action_12,
 action_13,
 action_14,
 action_15,
 action_16,
 action_17,
 action_18,
 action_19,
 action_20,
 action_21,
 action_22,
 action_23,
 action_24,
 action_25,
 action_26,
 action_27,
 action_28,
 action_29,
 action_30,
 action_31,
 action_32,
 action_33,
 action_34,
 action_35,
 action_36,
 action_37,
 action_38,
 action_39,
 action_40,
 action_41,
 action_42,
 action_43,
 action_44,
 action_45,
 action_46,
 action_47,
 action_48,
 action_49,
 action_50,
 action_51,
 action_52,
 action_53,
 action_54,
 action_55,
 action_56,
 action_57,
 action_58,
 action_59,
 action_60,
 action_61,
 action_62,
 action_63,
 action_64,
 action_65,
 action_66,
 action_67,
 action_68,
 action_69,
 action_70,
 action_71,
 action_72,
 action_73,
 action_74,
 action_75,
 action_76,
 action_77,
 action_78,
 action_79,
 action_80,
 action_81,
 action_82,
 action_83,
 action_84,
 action_85,
 action_86,
 action_87,
 action_88,
 action_89,
 action_90,
 action_91,
 action_92,
 action_93,
 action_94,
 action_95,
 action_96,
 action_97,
 action_98,
 action_99,
 action_100,
 action_101,
 action_102,
 action_103,
 action_104,
 action_105,
 action_106,
 action_107,
 action_108,
 action_109,
 action_110,
 action_111,
 action_112,
 action_113,
 action_114,
 action_115,
 action_116,
 action_117,
 action_118,
 action_119,
 action_120,
 action_121,
 action_122,
 action_123,
 action_124,
 action_125,
 action_126,
 action_127,
 action_128,
 action_129,
 action_130,
 action_131,
 action_132,
 action_133,
 action_134,
 action_135,
 action_136,
 action_137,
 action_138,
 action_139,
 action_140,
 action_141,
 action_142,
 action_143,
 action_144,
 action_145,
 action_146,
 action_147,
 action_148,
 action_149,
 action_150,
 action_151,
 action_152,
 action_153,
 action_154,
 action_155,
 action_156,
 action_157,
 action_158,
 action_159,
 action_160,
 action_161,
 action_162,
 action_163,
 action_164,
 action_165,
 action_166,
 action_167,
 action_168,
 action_169,
 action_170,
 action_171,
 action_172 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyReduce_16,
 happyReduce_17,
 happyReduce_18,
 happyReduce_19,
 happyReduce_20,
 happyReduce_21,
 happyReduce_22,
 happyReduce_23,
 happyReduce_24,
 happyReduce_25,
 happyReduce_26,
 happyReduce_27,
 happyReduce_28,
 happyReduce_29,
 happyReduce_30,
 happyReduce_31,
 happyReduce_32,
 happyReduce_33,
 happyReduce_34,
 happyReduce_35,
 happyReduce_36,
 happyReduce_37,
 happyReduce_38,
 happyReduce_39,
 happyReduce_40,
 happyReduce_41,
 happyReduce_42,
 happyReduce_43,
 happyReduce_44,
 happyReduce_45,
 happyReduce_46,
 happyReduce_47,
 happyReduce_48,
 happyReduce_49,
 happyReduce_50,
 happyReduce_51,
 happyReduce_52,
 happyReduce_53,
 happyReduce_54,
 happyReduce_55,
 happyReduce_56,
 happyReduce_57,
 happyReduce_58,
 happyReduce_59,
 happyReduce_60,
 happyReduce_61,
 happyReduce_62,
 happyReduce_63,
 happyReduce_64,
 happyReduce_65,
 happyReduce_66 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,363) ([0,0,0,16,0,0,0,32768,0,0,0,0,1024,0,0,0,32,0,0,0,0,1,0,0,0,0,256,0,0,0,0,8,0,0,0,14336,44,0,0,0,25024,1,0,0,0,1024,0,0,0,0,0,128,0,8192,4144,40716,5,0,33024,24577,11456,0,0,3080,768,358,0,16384,8288,15896,11,0,512,4,16384,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,513,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,49280,12288,5858,0,0,0,0,0,0,0,0,0,0,0,33024,24705,11512,0,0,8,0,0,0,16384,0,0,0,0,512,4,16384,0,0,16,0,0,0,0,0,0,0,0,1024,0,0,0,0,32,0,0,0,0,513,0,32,0,2048,12,26115,1,0,24640,6144,2864,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1540,384,179,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,512,0,0,0,0,0,0,0,0,1024,33286,46049,0,0,12320,3088,1439,0,0,0,0,32,0,0,0,0,1,0,0,0,2048,0,0,8192,0,0,0,0,0,0,0,0,4096,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,256,0,0,0,0,0,0,0,0,1,0,0,0,128,0,0,0,0,0,0,0,8192,0,0,0,0,32768,707,0,0,0,0,0,32,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,256,0,0,2052,0,128,0,8192,64,0,4,0,33024,24705,11512,0,0,512,0,0,0,16384,8288,15896,11,0,512,49411,23024,0,0,224,0,0,0,32768,16576,31792,22,0,1024,33286,46049,0,0,128,0,0,0,0,513,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,2072,53126,2,0,49280,12352,5756,0,0,16,0,0,0,32768,0,0,0,0,33024,24705,11512,0,0,16,0,0,0,0,2,0,0,0,4096,0,0,0,0,6160,34312,719,0,0,0,0,0,0,2048,0,0,0,0,0,0,0,0,0,33153,63584,44,0,16384,0,0,0,0,0,16384,0,0,0,0,16,0,0,0,0,0,0,0,49280,12352,5756,0,0,128,0,0,0,0,1024,0,0,0,512,0,0,0,0,64,0,0,0,0,34560,5,0,0,512,49411,23024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12320,3088,1439,0,0,33153,63584,44,0,0,0,0,0,0,0,16,0,0,0,770,61633,89,0,4096,2072,53126,2,0,256,0,0,0,0,8,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,0,0,0,0,64,0,0,0,32768,16576,31792,22,0,2048,0,0,0,0,64,0,0,0,0,16,0,0,0,0,0,16,0,0,24640,6176,2878,0,0,0,0,0,0,0,25024,1,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,33024,24705,11512,0,0,0,8192,0,0,0,0,16384,0,0,0,0,0,0,0,6160,34312,719,0,32768,16576,31792,22,0,2048,0,0,0,0,64,0,0,0,0,33153,63584,44,0,2048,1036,26563,1,0,0,0,0,0,0,770,61633,89,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListModule_internal","%start_pModule_internal","%start_pParam_internal","%start_pListParam_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pDischarge_internal","%start_pListVarIdent_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","Integer","VarIdent","Program","ListModule","Module","Param","ListParam","Import","ListImport","Decl","ListDecl","Discharge","ListVarIdent","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'let'","'module'","'namespace'","'open'","'over'","'private'","'refl'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\8658'","'\120140'","'\120793'","L_integ","L_VarIdent","%eof"]
        bit_start = st Prelude.* 75
        bit_end = (st Prelude.+ 1) Prelude.* 75
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..74]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (53) = happyShift action_66
action_0 (21) = happyGoto action_69
action_0 (22) = happyGoto action_70
action_0 (23) = happyGoto action_68
action_0 _ = happyReduce_19

action_1 (53) = happyShift action_66
action_1 (22) = happyGoto action_67
action_1 (23) = happyGoto action_68
action_1 _ = happyReduce_19

action_2 (53) = happyShift action_66
action_2 (23) = happyGoto action_65
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (37) = happyShift action_63
action_3 (24) = happyGoto action_64
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (37) = happyShift action_63
action_4 (24) = happyGoto action_61
action_4 (25) = happyGoto action_62
action_4 _ = happyReduce_23

action_5 (50) = happyShift action_59
action_5 (26) = happyGoto action_60
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (50) = happyShift action_59
action_6 (26) = happyGoto action_57
action_6 (27) = happyGoto action_58
action_6 _ = happyReduce_26

action_7 (47) = happyShift action_50
action_7 (48) = happyShift action_51
action_7 (49) = happyShift action_52
action_7 (54) = happyShift action_53
action_7 (55) = happyShift action_54
action_7 (57) = happyShift action_55
action_7 (28) = happyGoto action_56
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (47) = happyShift action_50
action_8 (48) = happyShift action_51
action_8 (49) = happyShift action_52
action_8 (54) = happyShift action_53
action_8 (55) = happyShift action_54
action_8 (57) = happyShift action_55
action_8 (28) = happyGoto action_48
action_8 (29) = happyGoto action_49
action_8 _ = happyReduce_34

action_9 (56) = happyShift action_47
action_9 (30) = happyGoto action_46
action_9 _ = happyReduce_37

action_10 (74) = happyShift action_22
action_10 (20) = happyGoto action_44
action_10 (31) = happyGoto action_45
action_10 _ = happyReduce_39

action_11 (37) = happyShift action_28
action_11 (44) = happyShift action_29
action_11 (45) = happyShift action_30
action_11 (52) = happyShift action_31
action_11 (58) = happyShift action_32
action_11 (59) = happyShift action_33
action_11 (64) = happyShift action_34
action_11 (65) = happyShift action_35
action_11 (66) = happyShift action_36
action_11 (67) = happyShift action_37
action_11 (68) = happyShift action_38
action_11 (71) = happyShift action_39
action_11 (72) = happyShift action_40
action_11 (74) = happyShift action_22
action_11 (20) = happyGoto action_23
action_11 (32) = happyGoto action_43
action_11 (33) = happyGoto action_25
action_11 (34) = happyGoto action_26
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (37) = happyShift action_28
action_12 (44) = happyShift action_29
action_12 (45) = happyShift action_30
action_12 (58) = happyShift action_32
action_12 (59) = happyShift action_33
action_12 (67) = happyShift action_37
action_12 (68) = happyShift action_38
action_12 (71) = happyShift action_39
action_12 (72) = happyShift action_40
action_12 (74) = happyShift action_22
action_12 (20) = happyGoto action_23
action_12 (33) = happyGoto action_42
action_12 (34) = happyGoto action_26
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (37) = happyShift action_28
action_13 (44) = happyShift action_29
action_13 (45) = happyShift action_30
action_13 (58) = happyShift action_32
action_13 (59) = happyShift action_33
action_13 (67) = happyShift action_37
action_13 (68) = happyShift action_38
action_13 (71) = happyShift action_39
action_13 (72) = happyShift action_40
action_13 (74) = happyShift action_22
action_13 (20) = happyGoto action_23
action_13 (34) = happyGoto action_41
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (37) = happyShift action_28
action_14 (44) = happyShift action_29
action_14 (45) = happyShift action_30
action_14 (52) = happyShift action_31
action_14 (58) = happyShift action_32
action_14 (59) = happyShift action_33
action_14 (64) = happyShift action_34
action_14 (65) = happyShift action_35
action_14 (66) = happyShift action_36
action_14 (67) = happyShift action_37
action_14 (68) = happyShift action_38
action_14 (71) = happyShift action_39
action_14 (72) = happyShift action_40
action_14 (74) = happyShift action_22
action_14 (20) = happyGoto action_23
action_14 (32) = happyGoto action_24
action_14 (33) = happyGoto action_25
action_14 (34) = happyGoto action_26
action_14 (35) = happyGoto action_27
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (37) = happyShift action_20
action_15 (46) = happyShift action_21
action_15 (74) = happyShift action_22
action_15 (20) = happyGoto action_18
action_15 (36) = happyGoto action_19
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (73) = happyShift action_17
action_16 _ = happyFail (happyExpListPerState 16)

action_17 _ = happyFail (happyExpListPerState 17)

action_18 _ = happyReduce_65

action_19 (75) = happyAccept
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (37) = happyShift action_20
action_20 (46) = happyShift action_21
action_20 (74) = happyShift action_22
action_20 (20) = happyGoto action_18
action_20 (36) = happyGoto action_99
action_20 _ = happyFail (happyExpListPerState 20)

action_21 _ = happyReduce_64

action_22 _ = happyReduce_17

action_23 _ = happyReduce_56

action_24 _ = happyReduce_63

action_25 (37) = happyShift action_28
action_25 (44) = happyShift action_29
action_25 (45) = happyShift action_30
action_25 (58) = happyShift action_32
action_25 (59) = happyShift action_33
action_25 (63) = happyShift action_97
action_25 (67) = happyShift action_37
action_25 (68) = happyShift action_38
action_25 (69) = happyShift action_98
action_25 (71) = happyShift action_39
action_25 (72) = happyShift action_40
action_25 (74) = happyShift action_22
action_25 (20) = happyGoto action_23
action_25 (34) = happyGoto action_86
action_25 _ = happyReduce_48

action_26 _ = happyReduce_50

action_27 (75) = happyAccept
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (37) = happyShift action_28
action_28 (44) = happyShift action_29
action_28 (45) = happyShift action_30
action_28 (52) = happyShift action_31
action_28 (58) = happyShift action_32
action_28 (59) = happyShift action_33
action_28 (64) = happyShift action_34
action_28 (65) = happyShift action_35
action_28 (66) = happyShift action_36
action_28 (67) = happyShift action_37
action_28 (68) = happyShift action_38
action_28 (71) = happyShift action_39
action_28 (72) = happyShift action_40
action_28 (74) = happyShift action_22
action_28 (20) = happyGoto action_23
action_28 (32) = happyGoto action_96
action_28 (33) = happyGoto action_25
action_28 (34) = happyGoto action_26
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (37) = happyShift action_95
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (37) = happyShift action_94
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (37) = happyShift action_20
action_31 (46) = happyShift action_21
action_31 (74) = happyShift action_22
action_31 (20) = happyGoto action_18
action_31 (36) = happyGoto action_93
action_31 _ = happyFail (happyExpListPerState 31)

action_32 (37) = happyShift action_92
action_32 _ = happyFail (happyExpListPerState 32)

action_33 _ = happyReduce_55

action_34 (37) = happyShift action_91
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (37) = happyShift action_90
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (37) = happyShift action_20
action_36 (46) = happyShift action_21
action_36 (74) = happyShift action_22
action_36 (20) = happyGoto action_18
action_36 (36) = happyGoto action_89
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (37) = happyShift action_28
action_37 (44) = happyShift action_29
action_37 (45) = happyShift action_30
action_37 (58) = happyShift action_32
action_37 (59) = happyShift action_33
action_37 (67) = happyShift action_37
action_37 (68) = happyShift action_38
action_37 (71) = happyShift action_39
action_37 (72) = happyShift action_40
action_37 (74) = happyShift action_22
action_37 (20) = happyGoto action_23
action_37 (34) = happyGoto action_88
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (37) = happyShift action_28
action_38 (44) = happyShift action_29
action_38 (45) = happyShift action_30
action_38 (58) = happyShift action_32
action_38 (59) = happyShift action_33
action_38 (67) = happyShift action_37
action_38 (68) = happyShift action_38
action_38 (71) = happyShift action_39
action_38 (72) = happyShift action_40
action_38 (74) = happyShift action_22
action_38 (20) = happyGoto action_23
action_38 (34) = happyGoto action_87
action_38 _ = happyFail (happyExpListPerState 38)

action_39 _ = happyReduce_53

action_40 _ = happyReduce_54

action_41 (75) = happyAccept
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (37) = happyShift action_28
action_42 (44) = happyShift action_29
action_42 (45) = happyShift action_30
action_42 (58) = happyShift action_32
action_42 (59) = happyShift action_33
action_42 (67) = happyShift action_37
action_42 (68) = happyShift action_38
action_42 (71) = happyShift action_39
action_42 (72) = happyShift action_40
action_42 (74) = happyShift action_22
action_42 (75) = happyAccept
action_42 (20) = happyGoto action_23
action_42 (34) = happyGoto action_86
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (75) = happyAccept
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (39) = happyShift action_85
action_44 _ = happyReduce_40

action_45 (75) = happyAccept
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (75) = happyAccept
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (37) = happyShift action_84
action_47 _ = happyFail (happyExpListPerState 47)

action_48 (42) = happyShift action_83
action_48 _ = happyReduce_35

action_49 (75) = happyAccept
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (37) = happyShift action_28
action_50 (44) = happyShift action_29
action_50 (45) = happyShift action_30
action_50 (52) = happyShift action_31
action_50 (58) = happyShift action_32
action_50 (59) = happyShift action_33
action_50 (64) = happyShift action_34
action_50 (65) = happyShift action_35
action_50 (66) = happyShift action_36
action_50 (67) = happyShift action_37
action_50 (68) = happyShift action_38
action_50 (71) = happyShift action_39
action_50 (72) = happyShift action_40
action_50 (74) = happyShift action_22
action_50 (20) = happyGoto action_23
action_50 (32) = happyGoto action_82
action_50 (33) = happyGoto action_25
action_50 (34) = happyGoto action_26
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (37) = happyShift action_28
action_51 (44) = happyShift action_29
action_51 (45) = happyShift action_30
action_51 (52) = happyShift action_31
action_51 (58) = happyShift action_32
action_51 (59) = happyShift action_33
action_51 (64) = happyShift action_34
action_51 (65) = happyShift action_35
action_51 (66) = happyShift action_36
action_51 (67) = happyShift action_37
action_51 (68) = happyShift action_38
action_51 (71) = happyShift action_39
action_51 (72) = happyShift action_40
action_51 (74) = happyShift action_22
action_51 (20) = happyGoto action_23
action_51 (32) = happyGoto action_81
action_51 (33) = happyGoto action_25
action_51 (34) = happyGoto action_26
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (74) = happyShift action_22
action_52 (20) = happyGoto action_80
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (74) = happyShift action_22
action_53 (20) = happyGoto action_79
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (74) = happyShift action_22
action_54 (20) = happyGoto action_78
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (49) = happyShift action_77
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (75) = happyAccept
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (42) = happyShift action_76
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (75) = happyAccept
action_58 _ = happyFail (happyExpListPerState 58)

action_59 (74) = happyShift action_22
action_59 (20) = happyGoto action_75
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (75) = happyAccept
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (37) = happyShift action_63
action_61 (24) = happyGoto action_61
action_61 (25) = happyGoto action_74
action_61 _ = happyReduce_23

action_62 (75) = happyAccept
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (74) = happyShift action_22
action_63 (20) = happyGoto action_73
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (75) = happyAccept
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (75) = happyAccept
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (74) = happyShift action_22
action_66 (20) = happyGoto action_72
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (75) = happyAccept
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (53) = happyShift action_66
action_68 (22) = happyGoto action_71
action_68 (23) = happyGoto action_68
action_68 _ = happyReduce_19

action_69 (75) = happyAccept
action_69 _ = happyFail (happyExpListPerState 69)

action_70 _ = happyReduce_18

action_71 _ = happyReduce_20

action_72 (37) = happyShift action_63
action_72 (24) = happyGoto action_61
action_72 (25) = happyGoto action_122
action_72 _ = happyReduce_23

action_73 (40) = happyShift action_121
action_73 _ = happyFail (happyExpListPerState 73)

action_74 _ = happyReduce_24

action_75 _ = happyReduce_25

action_76 (50) = happyShift action_59
action_76 (26) = happyGoto action_57
action_76 (27) = happyGoto action_120
action_76 _ = happyReduce_26

action_77 (74) = happyShift action_22
action_77 (20) = happyGoto action_119
action_77 _ = happyFail (happyExpListPerState 77)

action_78 _ = happyReduce_31

action_79 (60) = happyShift action_118
action_79 _ = happyFail (happyExpListPerState 79)

action_80 (56) = happyShift action_47
action_80 (30) = happyGoto action_117
action_80 _ = happyReduce_37

action_81 _ = happyReduce_33

action_82 (40) = happyShift action_116
action_82 _ = happyFail (happyExpListPerState 82)

action_83 (47) = happyShift action_50
action_83 (48) = happyShift action_51
action_83 (49) = happyShift action_52
action_83 (54) = happyShift action_53
action_83 (55) = happyShift action_54
action_83 (57) = happyShift action_55
action_83 (28) = happyGoto action_48
action_83 (29) = happyGoto action_115
action_83 _ = happyReduce_34

action_84 (74) = happyShift action_22
action_84 (20) = happyGoto action_44
action_84 (31) = happyGoto action_114
action_84 _ = happyReduce_39

action_85 (74) = happyShift action_22
action_85 (20) = happyGoto action_44
action_85 (31) = happyGoto action_113
action_85 _ = happyReduce_39

action_86 _ = happyReduce_49

action_87 _ = happyReduce_52

action_88 _ = happyReduce_51

action_89 (70) = happyShift action_112
action_89 _ = happyFail (happyExpListPerState 89)

action_90 (37) = happyShift action_20
action_90 (46) = happyShift action_21
action_90 (74) = happyShift action_22
action_90 (20) = happyGoto action_18
action_90 (36) = happyGoto action_111
action_90 _ = happyFail (happyExpListPerState 90)

action_91 (37) = happyShift action_20
action_91 (46) = happyShift action_21
action_91 (74) = happyShift action_22
action_91 (20) = happyGoto action_18
action_91 (36) = happyGoto action_110
action_91 _ = happyFail (happyExpListPerState 91)

action_92 (37) = happyShift action_28
action_92 (44) = happyShift action_29
action_92 (45) = happyShift action_30
action_92 (52) = happyShift action_31
action_92 (58) = happyShift action_32
action_92 (59) = happyShift action_33
action_92 (64) = happyShift action_34
action_92 (65) = happyShift action_35
action_92 (66) = happyShift action_36
action_92 (67) = happyShift action_37
action_92 (68) = happyShift action_38
action_92 (71) = happyShift action_39
action_92 (72) = happyShift action_40
action_92 (74) = happyShift action_22
action_92 (20) = happyGoto action_23
action_92 (32) = happyGoto action_109
action_92 (33) = happyGoto action_25
action_92 (34) = happyGoto action_26
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (43) = happyShift action_108
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (37) = happyShift action_28
action_94 (44) = happyShift action_29
action_94 (45) = happyShift action_30
action_94 (52) = happyShift action_31
action_94 (58) = happyShift action_32
action_94 (59) = happyShift action_33
action_94 (64) = happyShift action_34
action_94 (65) = happyShift action_35
action_94 (66) = happyShift action_36
action_94 (67) = happyShift action_37
action_94 (68) = happyShift action_38
action_94 (71) = happyShift action_39
action_94 (72) = happyShift action_40
action_94 (74) = happyShift action_22
action_94 (20) = happyGoto action_23
action_94 (32) = happyGoto action_107
action_94 (33) = happyGoto action_25
action_94 (34) = happyGoto action_26
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (37) = happyShift action_28
action_95 (44) = happyShift action_29
action_95 (45) = happyShift action_30
action_95 (52) = happyShift action_31
action_95 (58) = happyShift action_32
action_95 (59) = happyShift action_33
action_95 (64) = happyShift action_34
action_95 (65) = happyShift action_35
action_95 (66) = happyShift action_36
action_95 (67) = happyShift action_37
action_95 (68) = happyShift action_38
action_95 (71) = happyShift action_39
action_95 (72) = happyShift action_40
action_95 (74) = happyShift action_22
action_95 (20) = happyGoto action_23
action_95 (32) = happyGoto action_106
action_95 (33) = happyGoto action_25
action_95 (34) = happyGoto action_26
action_95 _ = happyFail (happyExpListPerState 95)

action_96 (38) = happyShift action_103
action_96 (39) = happyShift action_104
action_96 (40) = happyShift action_105
action_96 _ = happyFail (happyExpListPerState 96)

action_97 (37) = happyShift action_28
action_97 (44) = happyShift action_29
action_97 (45) = happyShift action_30
action_97 (52) = happyShift action_31
action_97 (58) = happyShift action_32
action_97 (59) = happyShift action_33
action_97 (64) = happyShift action_34
action_97 (65) = happyShift action_35
action_97 (66) = happyShift action_36
action_97 (67) = happyShift action_37
action_97 (68) = happyShift action_38
action_97 (71) = happyShift action_39
action_97 (72) = happyShift action_40
action_97 (74) = happyShift action_22
action_97 (20) = happyGoto action_23
action_97 (32) = happyGoto action_102
action_97 (33) = happyGoto action_25
action_97 (34) = happyGoto action_26
action_97 _ = happyFail (happyExpListPerState 97)

action_98 (37) = happyShift action_28
action_98 (44) = happyShift action_29
action_98 (45) = happyShift action_30
action_98 (52) = happyShift action_31
action_98 (58) = happyShift action_32
action_98 (59) = happyShift action_33
action_98 (64) = happyShift action_34
action_98 (65) = happyShift action_35
action_98 (66) = happyShift action_36
action_98 (67) = happyShift action_37
action_98 (68) = happyShift action_38
action_98 (71) = happyShift action_39
action_98 (72) = happyShift action_40
action_98 (74) = happyShift action_22
action_98 (20) = happyGoto action_23
action_98 (32) = happyGoto action_101
action_98 (33) = happyGoto action_25
action_98 (34) = happyGoto action_26
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (39) = happyShift action_100
action_99 _ = happyFail (happyExpListPerState 99)

action_100 (37) = happyShift action_20
action_100 (46) = happyShift action_21
action_100 (74) = happyShift action_22
action_100 (20) = happyGoto action_18
action_100 (36) = happyGoto action_139
action_100 _ = happyFail (happyExpListPerState 100)

action_101 _ = happyReduce_46

action_102 _ = happyReduce_47

action_103 _ = happyReduce_62

action_104 (37) = happyShift action_28
action_104 (44) = happyShift action_29
action_104 (45) = happyShift action_30
action_104 (52) = happyShift action_31
action_104 (58) = happyShift action_32
action_104 (59) = happyShift action_33
action_104 (64) = happyShift action_34
action_104 (65) = happyShift action_35
action_104 (66) = happyShift action_36
action_104 (67) = happyShift action_37
action_104 (68) = happyShift action_38
action_104 (71) = happyShift action_39
action_104 (72) = happyShift action_40
action_104 (74) = happyShift action_22
action_104 (20) = happyGoto action_23
action_104 (32) = happyGoto action_138
action_104 (33) = happyGoto action_25
action_104 (34) = happyGoto action_26
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (37) = happyShift action_28
action_105 (44) = happyShift action_29
action_105 (45) = happyShift action_30
action_105 (52) = happyShift action_31
action_105 (58) = happyShift action_32
action_105 (59) = happyShift action_33
action_105 (64) = happyShift action_34
action_105 (65) = happyShift action_35
action_105 (66) = happyShift action_36
action_105 (67) = happyShift action_37
action_105 (68) = happyShift action_38
action_105 (71) = happyShift action_39
action_105 (72) = happyShift action_40
action_105 (74) = happyShift action_22
action_105 (20) = happyGoto action_23
action_105 (32) = happyGoto action_137
action_105 (33) = happyGoto action_25
action_105 (34) = happyGoto action_26
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (39) = happyShift action_136
action_106 _ = happyFail (happyExpListPerState 106)

action_107 (39) = happyShift action_135
action_107 _ = happyFail (happyExpListPerState 107)

action_108 (37) = happyShift action_28
action_108 (44) = happyShift action_29
action_108 (45) = happyShift action_30
action_108 (52) = happyShift action_31
action_108 (58) = happyShift action_32
action_108 (59) = happyShift action_33
action_108 (64) = happyShift action_34
action_108 (65) = happyShift action_35
action_108 (66) = happyShift action_36
action_108 (67) = happyShift action_37
action_108 (68) = happyShift action_38
action_108 (71) = happyShift action_39
action_108 (72) = happyShift action_40
action_108 (74) = happyShift action_22
action_108 (20) = happyGoto action_23
action_108 (32) = happyGoto action_134
action_108 (33) = happyGoto action_25
action_108 (34) = happyGoto action_26
action_108 _ = happyFail (happyExpListPerState 108)

action_109 (38) = happyShift action_133
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (40) = happyShift action_132
action_110 _ = happyFail (happyExpListPerState 110)

action_111 (40) = happyShift action_131
action_111 _ = happyFail (happyExpListPerState 111)

action_112 (37) = happyShift action_28
action_112 (44) = happyShift action_29
action_112 (45) = happyShift action_30
action_112 (52) = happyShift action_31
action_112 (58) = happyShift action_32
action_112 (59) = happyShift action_33
action_112 (64) = happyShift action_34
action_112 (65) = happyShift action_35
action_112 (66) = happyShift action_36
action_112 (67) = happyShift action_37
action_112 (68) = happyShift action_38
action_112 (71) = happyShift action_39
action_112 (72) = happyShift action_40
action_112 (74) = happyShift action_22
action_112 (20) = happyGoto action_23
action_112 (32) = happyGoto action_24
action_112 (33) = happyGoto action_25
action_112 (34) = happyGoto action_26
action_112 (35) = happyGoto action_130
action_112 _ = happyFail (happyExpListPerState 112)

action_113 _ = happyReduce_41

action_114 (38) = happyShift action_129
action_114 _ = happyFail (happyExpListPerState 114)

action_115 _ = happyReduce_36

action_116 (37) = happyShift action_28
action_116 (44) = happyShift action_29
action_116 (45) = happyShift action_30
action_116 (52) = happyShift action_31
action_116 (58) = happyShift action_32
action_116 (59) = happyShift action_33
action_116 (64) = happyShift action_34
action_116 (65) = happyShift action_35
action_116 (66) = happyShift action_36
action_116 (67) = happyShift action_37
action_116 (68) = happyShift action_38
action_116 (71) = happyShift action_39
action_116 (72) = happyShift action_40
action_116 (74) = happyShift action_22
action_116 (20) = happyGoto action_23
action_116 (32) = happyGoto action_128
action_116 (33) = happyGoto action_25
action_116 (34) = happyGoto action_26
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (40) = happyShift action_127
action_117 _ = happyFail (happyExpListPerState 117)

action_118 (61) = happyShift action_126
action_118 _ = happyFail (happyExpListPerState 118)

action_119 (56) = happyShift action_47
action_119 (30) = happyGoto action_125
action_119 _ = happyReduce_37

action_120 _ = happyReduce_27

action_121 (37) = happyShift action_28
action_121 (44) = happyShift action_29
action_121 (45) = happyShift action_30
action_121 (52) = happyShift action_31
action_121 (58) = happyShift action_32
action_121 (59) = happyShift action_33
action_121 (64) = happyShift action_34
action_121 (65) = happyShift action_35
action_121 (66) = happyShift action_36
action_121 (67) = happyShift action_37
action_121 (68) = happyShift action_38
action_121 (71) = happyShift action_39
action_121 (72) = happyShift action_40
action_121 (74) = happyShift action_22
action_121 (20) = happyGoto action_23
action_121 (32) = happyGoto action_124
action_121 (33) = happyGoto action_25
action_121 (34) = happyGoto action_26
action_121 _ = happyFail (happyExpListPerState 121)

action_122 (42) = happyShift action_123
action_122 _ = happyFail (happyExpListPerState 122)

action_123 (50) = happyShift action_59
action_123 (26) = happyGoto action_57
action_123 (27) = happyGoto action_152
action_123 _ = happyReduce_26

action_124 (38) = happyShift action_151
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (40) = happyShift action_150
action_125 _ = happyFail (happyExpListPerState 125)

action_126 (47) = happyShift action_50
action_126 (48) = happyShift action_51
action_126 (49) = happyShift action_52
action_126 (54) = happyShift action_53
action_126 (55) = happyShift action_54
action_126 (57) = happyShift action_55
action_126 (28) = happyGoto action_48
action_126 (29) = happyGoto action_149
action_126 _ = happyReduce_34

action_127 (37) = happyShift action_28
action_127 (44) = happyShift action_29
action_127 (45) = happyShift action_30
action_127 (52) = happyShift action_31
action_127 (58) = happyShift action_32
action_127 (59) = happyShift action_33
action_127 (64) = happyShift action_34
action_127 (65) = happyShift action_35
action_127 (66) = happyShift action_36
action_127 (67) = happyShift action_37
action_127 (68) = happyShift action_38
action_127 (71) = happyShift action_39
action_127 (72) = happyShift action_40
action_127 (74) = happyShift action_22
action_127 (20) = happyGoto action_23
action_127 (32) = happyGoto action_148
action_127 (33) = happyGoto action_25
action_127 (34) = happyGoto action_26
action_127 _ = happyFail (happyExpListPerState 127)

action_128 _ = happyReduce_32

action_129 _ = happyReduce_38

action_130 _ = happyReduce_44

action_131 (37) = happyShift action_28
action_131 (44) = happyShift action_29
action_131 (45) = happyShift action_30
action_131 (52) = happyShift action_31
action_131 (58) = happyShift action_32
action_131 (59) = happyShift action_33
action_131 (64) = happyShift action_34
action_131 (65) = happyShift action_35
action_131 (66) = happyShift action_36
action_131 (67) = happyShift action_37
action_131 (68) = happyShift action_38
action_131 (71) = happyShift action_39
action_131 (72) = happyShift action_40
action_131 (74) = happyShift action_22
action_131 (20) = happyGoto action_23
action_131 (32) = happyGoto action_147
action_131 (33) = happyGoto action_25
action_131 (34) = happyGoto action_26
action_131 _ = happyFail (happyExpListPerState 131)

action_132 (37) = happyShift action_28
action_132 (44) = happyShift action_29
action_132 (45) = happyShift action_30
action_132 (52) = happyShift action_31
action_132 (58) = happyShift action_32
action_132 (59) = happyShift action_33
action_132 (64) = happyShift action_34
action_132 (65) = happyShift action_35
action_132 (66) = happyShift action_36
action_132 (67) = happyShift action_37
action_132 (68) = happyShift action_38
action_132 (71) = happyShift action_39
action_132 (72) = happyShift action_40
action_132 (74) = happyShift action_22
action_132 (20) = happyGoto action_23
action_132 (32) = happyGoto action_146
action_132 (33) = happyGoto action_25
action_132 (34) = happyGoto action_26
action_132 _ = happyFail (happyExpListPerState 132)

action_133 _ = happyReduce_58

action_134 (51) = happyShift action_145
action_134 _ = happyFail (happyExpListPerState 134)

action_135 (37) = happyShift action_28
action_135 (44) = happyShift action_29
action_135 (45) = happyShift action_30
action_135 (52) = happyShift action_31
action_135 (58) = happyShift action_32
action_135 (59) = happyShift action_33
action_135 (64) = happyShift action_34
action_135 (65) = happyShift action_35
action_135 (66) = happyShift action_36
action_135 (67) = happyShift action_37
action_135 (68) = happyShift action_38
action_135 (71) = happyShift action_39
action_135 (72) = happyShift action_40
action_135 (74) = happyShift action_22
action_135 (20) = happyGoto action_23
action_135 (32) = happyGoto action_144
action_135 (33) = happyGoto action_25
action_135 (34) = happyGoto action_26
action_135 _ = happyFail (happyExpListPerState 135)

action_136 (37) = happyShift action_28
action_136 (44) = happyShift action_29
action_136 (45) = happyShift action_30
action_136 (52) = happyShift action_31
action_136 (58) = happyShift action_32
action_136 (59) = happyShift action_33
action_136 (64) = happyShift action_34
action_136 (65) = happyShift action_35
action_136 (66) = happyShift action_36
action_136 (67) = happyShift action_37
action_136 (68) = happyShift action_38
action_136 (71) = happyShift action_39
action_136 (72) = happyShift action_40
action_136 (74) = happyShift action_22
action_136 (20) = happyGoto action_23
action_136 (32) = happyGoto action_143
action_136 (33) = happyGoto action_25
action_136 (34) = happyGoto action_26
action_136 _ = happyFail (happyExpListPerState 136)

action_137 (38) = happyShift action_142
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (38) = happyShift action_141
action_138 _ = happyFail (happyExpListPerState 138)

action_139 (38) = happyShift action_140
action_139 _ = happyFail (happyExpListPerState 139)

action_140 _ = happyReduce_66

action_141 _ = happyReduce_60

action_142 _ = happyReduce_61

action_143 (39) = happyShift action_161
action_143 _ = happyFail (happyExpListPerState 143)

action_144 (39) = happyShift action_160
action_144 _ = happyFail (happyExpListPerState 144)

action_145 (37) = happyShift action_28
action_145 (44) = happyShift action_29
action_145 (45) = happyShift action_30
action_145 (52) = happyShift action_31
action_145 (58) = happyShift action_32
action_145 (59) = happyShift action_33
action_145 (64) = happyShift action_34
action_145 (65) = happyShift action_35
action_145 (66) = happyShift action_36
action_145 (67) = happyShift action_37
action_145 (68) = happyShift action_38
action_145 (71) = happyShift action_39
action_145 (72) = happyShift action_40
action_145 (74) = happyShift action_22
action_145 (20) = happyGoto action_23
action_145 (32) = happyGoto action_24
action_145 (33) = happyGoto action_25
action_145 (34) = happyGoto action_26
action_145 (35) = happyGoto action_159
action_145 _ = happyFail (happyExpListPerState 145)

action_146 (38) = happyShift action_158
action_146 _ = happyFail (happyExpListPerState 146)

action_147 (38) = happyShift action_157
action_147 _ = happyFail (happyExpListPerState 147)

action_148 (41) = happyShift action_156
action_148 _ = happyFail (happyExpListPerState 148)

action_149 (62) = happyShift action_155
action_149 _ = happyFail (happyExpListPerState 149)

action_150 (37) = happyShift action_28
action_150 (44) = happyShift action_29
action_150 (45) = happyShift action_30
action_150 (52) = happyShift action_31
action_150 (58) = happyShift action_32
action_150 (59) = happyShift action_33
action_150 (64) = happyShift action_34
action_150 (65) = happyShift action_35
action_150 (66) = happyShift action_36
action_150 (67) = happyShift action_37
action_150 (68) = happyShift action_38
action_150 (71) = happyShift action_39
action_150 (72) = happyShift action_40
action_150 (74) = happyShift action_22
action_150 (20) = happyGoto action_23
action_150 (32) = happyGoto action_154
action_150 (33) = happyGoto action_25
action_150 (34) = happyGoto action_26
action_150 _ = happyFail (happyExpListPerState 150)

action_151 _ = happyReduce_22

action_152 (47) = happyShift action_50
action_152 (48) = happyShift action_51
action_152 (49) = happyShift action_52
action_152 (54) = happyShift action_53
action_152 (55) = happyShift action_54
action_152 (57) = happyShift action_55
action_152 (28) = happyGoto action_48
action_152 (29) = happyGoto action_153
action_152 _ = happyReduce_34

action_153 _ = happyReduce_21

action_154 (41) = happyShift action_167
action_154 _ = happyFail (happyExpListPerState 154)

action_155 _ = happyReduce_30

action_156 (37) = happyShift action_28
action_156 (44) = happyShift action_29
action_156 (45) = happyShift action_30
action_156 (52) = happyShift action_31
action_156 (58) = happyShift action_32
action_156 (59) = happyShift action_33
action_156 (64) = happyShift action_34
action_156 (65) = happyShift action_35
action_156 (66) = happyShift action_36
action_156 (67) = happyShift action_37
action_156 (68) = happyShift action_38
action_156 (71) = happyShift action_39
action_156 (72) = happyShift action_40
action_156 (74) = happyShift action_22
action_156 (20) = happyGoto action_23
action_156 (32) = happyGoto action_166
action_156 (33) = happyGoto action_25
action_156 (34) = happyGoto action_26
action_156 _ = happyFail (happyExpListPerState 156)

action_157 (63) = happyShift action_165
action_157 _ = happyFail (happyExpListPerState 157)

action_158 (69) = happyShift action_164
action_158 _ = happyFail (happyExpListPerState 158)

action_159 _ = happyReduce_45

action_160 (37) = happyShift action_28
action_160 (44) = happyShift action_29
action_160 (45) = happyShift action_30
action_160 (52) = happyShift action_31
action_160 (58) = happyShift action_32
action_160 (59) = happyShift action_33
action_160 (64) = happyShift action_34
action_160 (65) = happyShift action_35
action_160 (66) = happyShift action_36
action_160 (67) = happyShift action_37
action_160 (68) = happyShift action_38
action_160 (71) = happyShift action_39
action_160 (72) = happyShift action_40
action_160 (74) = happyShift action_22
action_160 (20) = happyGoto action_23
action_160 (32) = happyGoto action_163
action_160 (33) = happyGoto action_25
action_160 (34) = happyGoto action_26
action_160 _ = happyFail (happyExpListPerState 160)

action_161 (37) = happyShift action_28
action_161 (44) = happyShift action_29
action_161 (45) = happyShift action_30
action_161 (52) = happyShift action_31
action_161 (58) = happyShift action_32
action_161 (59) = happyShift action_33
action_161 (64) = happyShift action_34
action_161 (65) = happyShift action_35
action_161 (66) = happyShift action_36
action_161 (67) = happyShift action_37
action_161 (68) = happyShift action_38
action_161 (71) = happyShift action_39
action_161 (72) = happyShift action_40
action_161 (74) = happyShift action_22
action_161 (20) = happyGoto action_23
action_161 (32) = happyGoto action_162
action_161 (33) = happyGoto action_25
action_161 (34) = happyGoto action_26
action_161 _ = happyFail (happyExpListPerState 161)

action_162 (38) = happyShift action_172
action_162 _ = happyFail (happyExpListPerState 162)

action_163 (38) = happyShift action_171
action_163 _ = happyFail (happyExpListPerState 163)

action_164 (37) = happyShift action_28
action_164 (44) = happyShift action_29
action_164 (45) = happyShift action_30
action_164 (52) = happyShift action_31
action_164 (58) = happyShift action_32
action_164 (59) = happyShift action_33
action_164 (64) = happyShift action_34
action_164 (65) = happyShift action_35
action_164 (66) = happyShift action_36
action_164 (67) = happyShift action_37
action_164 (68) = happyShift action_38
action_164 (71) = happyShift action_39
action_164 (72) = happyShift action_40
action_164 (74) = happyShift action_22
action_164 (20) = happyGoto action_23
action_164 (32) = happyGoto action_24
action_164 (33) = happyGoto action_25
action_164 (34) = happyGoto action_26
action_164 (35) = happyGoto action_170
action_164 _ = happyFail (happyExpListPerState 164)

action_165 (37) = happyShift action_28
action_165 (44) = happyShift action_29
action_165 (45) = happyShift action_30
action_165 (52) = happyShift action_31
action_165 (58) = happyShift action_32
action_165 (59) = happyShift action_33
action_165 (64) = happyShift action_34
action_165 (65) = happyShift action_35
action_165 (66) = happyShift action_36
action_165 (67) = happyShift action_37
action_165 (68) = happyShift action_38
action_165 (71) = happyShift action_39
action_165 (72) = happyShift action_40
action_165 (74) = happyShift action_22
action_165 (20) = happyGoto action_23
action_165 (32) = happyGoto action_24
action_165 (33) = happyGoto action_25
action_165 (34) = happyGoto action_26
action_165 (35) = happyGoto action_169
action_165 _ = happyFail (happyExpListPerState 165)

action_166 _ = happyReduce_28

action_167 (37) = happyShift action_28
action_167 (44) = happyShift action_29
action_167 (45) = happyShift action_30
action_167 (52) = happyShift action_31
action_167 (58) = happyShift action_32
action_167 (59) = happyShift action_33
action_167 (64) = happyShift action_34
action_167 (65) = happyShift action_35
action_167 (66) = happyShift action_36
action_167 (67) = happyShift action_37
action_167 (68) = happyShift action_38
action_167 (71) = happyShift action_39
action_167 (72) = happyShift action_40
action_167 (74) = happyShift action_22
action_167 (20) = happyGoto action_23
action_167 (32) = happyGoto action_168
action_167 (33) = happyGoto action_25
action_167 (34) = happyGoto action_26
action_167 _ = happyFail (happyExpListPerState 167)

action_168 _ = happyReduce_29

action_169 _ = happyReduce_43

action_170 _ = happyReduce_42

action_171 _ = happyReduce_59

action_172 _ = happyReduce_57

happyReduce_16 = happySpecReduce_1  19 happyReduction_16
happyReduction_16 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (read (tokenText happy_var_1)) :: Integer)
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  20 happyReduction_17
happyReduction_17 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn20
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_1  21 happyReduction_18
happyReduction_18 (HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn21
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_18 _  = notHappyAtAll 

happyReduce_19 = happySpecReduce_0  22 happyReduction_19
happyReduction_19  =  HappyAbsSyn22
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_20 = happySpecReduce_2  22 happyReduction_20
happyReduction_20 (HappyAbsSyn22  happy_var_2)
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn22
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_20 _ _  = notHappyAtAll 

happyReduce_21 = happyReduce 6 23 happyReduction_21
happyReduction_21 ((HappyAbsSyn29  happy_var_6) `HappyStk`
	(HappyAbsSyn27  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn25  happy_var_3) `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_22 = happyReduce 5 24 happyReduction_22
happyReduction_22 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn24
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AParam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_23 = happySpecReduce_0  25 happyReduction_23
happyReduction_23  =  HappyAbsSyn25
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_24 = happySpecReduce_2  25 happyReduction_24
happyReduction_24 (HappyAbsSyn25  happy_var_2)
	(HappyAbsSyn24  happy_var_1)
	 =  HappyAbsSyn25
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_2  26 happyReduction_25
happyReduction_25 (HappyAbsSyn20  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn26
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_25 _ _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_0  27 happyReduction_26
happyReduction_26  =  HappyAbsSyn27
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_27 = happySpecReduce_3  27 happyReduction_27
happyReduction_27 (HappyAbsSyn27  happy_var_3)
	_
	(HappyAbsSyn26  happy_var_1)
	 =  HappyAbsSyn27
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_27 _ _ _  = notHappyAtAll 

happyReduce_28 = happyReduce 7 28 happyReduction_28
happyReduction_28 ((HappyAbsSyn32  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn30  happy_var_3) `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 8 28 happyReduction_29
happyReduction_29 ((HappyAbsSyn32  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn30  happy_var_4) `HappyStk`
	(HappyAbsSyn20  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_30 = happyReduce 6 28 happyReduction_30
happyReduction_30 (_ `HappyStk`
	(HappyAbsSyn29  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn20  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_31 = happySpecReduce_2  28 happyReduction_31
happyReduction_31 (HappyAbsSyn20  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_31 _ _  = notHappyAtAll 

happyReduce_32 = happyReduce 4 28 happyReduction_32
happyReduction_32 ((HappyAbsSyn32  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_33 = happySpecReduce_2  28 happyReduction_33
happyReduction_33 (HappyAbsSyn32  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn28
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_33 _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_0  29 happyReduction_34
happyReduction_34  =  HappyAbsSyn29
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_35 = happySpecReduce_1  29 happyReduction_35
happyReduction_35 (HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_35 _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_3  29 happyReduction_36
happyReduction_36 (HappyAbsSyn29  happy_var_3)
	_
	(HappyAbsSyn28  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_0  30 happyReduction_37
happyReduction_37  =  HappyAbsSyn30
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoDischarge Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_38 = happyReduce 4 30 happyReduction_38
happyReduction_38 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn30
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DischargeOver (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_39 = happySpecReduce_0  31 happyReduction_39
happyReduction_39  =  HappyAbsSyn31
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_40 = happySpecReduce_1  31 happyReduction_40
happyReduction_40 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_40 _  = notHappyAtAll 

happyReduce_41 = happySpecReduce_3  31 happyReduction_41
happyReduction_41 (HappyAbsSyn31  happy_var_3)
	_
	(HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_41 _ _ _  = notHappyAtAll 

happyReduce_42 = happyReduce 8 32 happyReduction_42
happyReduction_42 ((HappyAbsSyn35  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn36  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_43 = happyReduce 8 32 happyReduction_43
happyReduction_43 ((HappyAbsSyn35  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn36  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_44 = happyReduce 4 32 happyReduction_44
happyReduction_44 ((HappyAbsSyn35  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn36  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_45 = happyReduce 6 32 happyReduction_45
happyReduction_45 ((HappyAbsSyn35  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn36  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_46 = happySpecReduce_3  32 happyReduction_46
happyReduction_46 (HappyAbsSyn32  happy_var_3)
	_
	(HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_3  32 happyReduction_47
happyReduction_47 (HappyAbsSyn32  happy_var_3)
	_
	(HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_47 _ _ _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_1  32 happyReduction_48
happyReduction_48 (HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_48 _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_2  33 happyReduction_49
happyReduction_49 (HappyAbsSyn32  happy_var_2)
	(HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_49 _ _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_1  33 happyReduction_50
happyReduction_50 (HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_50 _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_2  34 happyReduction_51
happyReduction_51 (HappyAbsSyn32  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_51 _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_2  34 happyReduction_52
happyReduction_52 (HappyAbsSyn32  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_52 _ _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  34 happyReduction_53
happyReduction_53 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_1  34 happyReduction_54
happyReduction_54 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_54 _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_1  34 happyReduction_55
happyReduction_55 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_1  34 happyReduction_56
happyReduction_56 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn32
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_56 _  = notHappyAtAll 

happyReduce_57 = happyReduce 8 34 happyReduction_57
happyReduction_57 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_58 = happyReduce 4 34 happyReduction_58
happyReduction_58 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_59 = happyReduce 8 34 happyReduction_59
happyReduction_59 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_60 = happyReduce 5 34 happyReduction_60
happyReduction_60 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_61 = happyReduce 5 34 happyReduction_61
happyReduction_61 (_ `HappyStk`
	(HappyAbsSyn32  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn32  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_62 = happySpecReduce_3  34 happyReduction_62
happyReduction_62 _
	(HappyAbsSyn32  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_62 _ _ _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  35 happyReduction_63
happyReduction_63 (HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn35
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_1  36 happyReduction_64
happyReduction_64 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn36
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_64 _  = notHappyAtAll 

happyReduce_65 = happySpecReduce_1  36 happyReduction_65
happyReduction_65 (HappyAbsSyn20  happy_var_1)
	 =  HappyAbsSyn36
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_65 _  = notHappyAtAll 

happyReduce_66 = happyReduce 5 36 happyReduction_66
happyReduction_66 (_ `HappyStk`
	(HappyAbsSyn36  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn36  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn36
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 75 75 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 37;
	PT _ (TS _ 2) -> cont 38;
	PT _ (TS _ 3) -> cont 39;
	PT _ (TS _ 4) -> cont 40;
	PT _ (TS _ 5) -> cont 41;
	PT _ (TS _ 6) -> cont 42;
	PT _ (TS _ 7) -> cont 43;
	PT _ (TS _ 8) -> cont 44;
	PT _ (TS _ 9) -> cont 45;
	PT _ (TS _ 10) -> cont 46;
	PT _ (TS _ 11) -> cont 47;
	PT _ (TS _ 12) -> cont 48;
	PT _ (TS _ 13) -> cont 49;
	PT _ (TS _ 14) -> cont 50;
	PT _ (TS _ 15) -> cont 51;
	PT _ (TS _ 16) -> cont 52;
	PT _ (TS _ 17) -> cont 53;
	PT _ (TS _ 18) -> cont 54;
	PT _ (TS _ 19) -> cont 55;
	PT _ (TS _ 20) -> cont 56;
	PT _ (TS _ 21) -> cont 57;
	PT _ (TS _ 22) -> cont 58;
	PT _ (TS _ 23) -> cont 59;
	PT _ (TS _ 24) -> cont 60;
	PT _ (TS _ 25) -> cont 61;
	PT _ (TS _ 26) -> cont 62;
	PT _ (TS _ 27) -> cont 63;
	PT _ (TS _ 28) -> cont 64;
	PT _ (TS _ 29) -> cont 65;
	PT _ (TS _ 30) -> cont 66;
	PT _ (TS _ 31) -> cont 67;
	PT _ (TS _ 32) -> cont 68;
	PT _ (TS _ 33) -> cont 69;
	PT _ (TS _ 34) -> cont 70;
	PT _ (TS _ 35) -> cont 71;
	PT _ (TS _ 36) -> cont 72;
	PT _ (TI _) -> cont 73;
	PT _ (T_VarIdent _) -> cont 74;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 75 tk tks = happyError' (tks, explist)
happyError_ explist _ tk tks = happyError' ((tk:tks), explist)

happyThen :: () => Err a -> (a -> Err b) -> Err b
happyThen = ((>>=))
happyReturn :: () => a -> Err a
happyReturn = (return)
happyThen1 m k tks = ((>>=)) m (\a -> k a tks)
happyReturn1 :: () => a -> b -> Err a
happyReturn1 = \a tks -> (return) a
happyError' :: () => ([(Token)], [Prelude.String]) -> Err a
happyError' = (\(tokens, _) -> happyError tokens)
pProgram_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn21 z -> happyReturn z; _other -> notHappyAtAll })

pListModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn22 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

pParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn24 z -> happyReturn z; _other -> notHappyAtAll })

pListParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn25 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn26 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn27 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn28 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn29 z -> happyReturn z; _other -> notHappyAtAll })

pDischarge_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn30 z -> happyReturn z; _other -> notHappyAtAll })

pListVarIdent_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_12 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_13 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_14 tks) (\x -> case x of {HappyAbsSyn35 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_15 tks) (\x -> case x of {HappyAbsSyn36 z -> happyReturn z; _other -> notHappyAtAll })

happySeq = happyDontSeq


type Err = Either String

happyError :: [Token] -> Err a
happyError ts = Left $
  "syntax error at " ++ tokenPos ts ++
  case ts of
    []      -> []
    [Err _] -> " due to lexer error"
    t:_     -> " before `" ++ (prToken t) ++ "'"

myLexer :: String -> [Token]
myLexer = tokens

-- Entrypoints

pProgram :: [Token] -> Err Language.MLTT.Syntax.Abs.Program
pProgram = fmap snd . pProgram_internal

pListModule :: [Token] -> Err [Language.MLTT.Syntax.Abs.Module]
pListModule = fmap snd . pListModule_internal

pModule :: [Token] -> Err Language.MLTT.Syntax.Abs.Module
pModule = fmap snd . pModule_internal

pParam :: [Token] -> Err Language.MLTT.Syntax.Abs.Param
pParam = fmap snd . pParam_internal

pListParam :: [Token] -> Err [Language.MLTT.Syntax.Abs.Param]
pListParam = fmap snd . pListParam_internal

pImport :: [Token] -> Err Language.MLTT.Syntax.Abs.Import
pImport = fmap snd . pImport_internal

pListImport :: [Token] -> Err [Language.MLTT.Syntax.Abs.Import]
pListImport = fmap snd . pListImport_internal

pDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.Decl
pDecl = fmap snd . pDecl_internal

pListDecl :: [Token] -> Err [Language.MLTT.Syntax.Abs.Decl]
pListDecl = fmap snd . pListDecl_internal

pDischarge :: [Token] -> Err Language.MLTT.Syntax.Abs.Discharge
pDischarge = fmap snd . pDischarge_internal

pListVarIdent :: [Token] -> Err [Language.MLTT.Syntax.Abs.VarIdent]
pListVarIdent = fmap snd . pListVarIdent_internal

pTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm = fmap snd . pTerm_internal

pTerm1 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm1 = fmap snd . pTerm1_internal

pTerm2 :: [Token] -> Err Language.MLTT.Syntax.Abs.Term
pTerm2 = fmap snd . pTerm2_internal

pScopedTerm :: [Token] -> Err Language.MLTT.Syntax.Abs.ScopedTerm
pScopedTerm = fmap snd . pScopedTerm_internal

pPattern :: [Token] -> Err Language.MLTT.Syntax.Abs.Pattern
pPattern = fmap snd . pPattern_internal
{-# LINE 1 "templates/GenericTemplate.hs" #-}
-- $Id: GenericTemplate.hs,v 1.26 2005/01/14 14:47:22 simonmar Exp $










































data Happy_IntList = HappyCons Prelude.Int Happy_IntList








































infixr 9 `HappyStk`
data HappyStk a = HappyStk a (HappyStk a)

-----------------------------------------------------------------------------
-- starting the parse

happyParse start_state = happyNewToken start_state notHappyAtAll notHappyAtAll

-----------------------------------------------------------------------------
-- Accepting the parse

-- If the current token is ERROR_TOK, it means we've just accepted a partial
-- parse (a %partial parser).  We must ignore the saved token on the top of
-- the stack in this case.
happyAccept (1) tk st sts (_ `HappyStk` ans `HappyStk` _) =
        happyReturn1 ans
happyAccept j tk st sts (HappyStk ans _) = 
         (happyReturn1 ans)

-----------------------------------------------------------------------------
-- Arrays only: do the next action









































indexShortOffAddr arr off = arr Happy_Data_Array.! off


{-# INLINE happyLt #-}
happyLt x y = (x Prelude.< y)






readArrayBit arr bit =
    Bits.testBit (indexShortOffAddr arr (bit `Prelude.div` 16)) (bit `Prelude.mod` 16)






-----------------------------------------------------------------------------
-- HappyState data type (not arrays)



newtype HappyState b c = HappyState
        (Prelude.Int ->                    -- token number
         Prelude.Int ->                    -- token number (yes, again)
         b ->                           -- token semantic value
         HappyState b c ->              -- current state
         [HappyState b c] ->            -- state stack
         c)



-----------------------------------------------------------------------------
-- Shifting a token

happyShift new_state (1) tk st sts stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--     trace "shifting the error token" $
     new_state i i tk (HappyState (new_state)) ((st):(sts)) (stk)

happyShift new_state i tk st sts stk =
     happyNewToken new_state ((st):(sts)) ((HappyTerminal (tk))`HappyStk`stk)

-- happyReduce is specialised for the common cases.

happySpecReduce_0 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_0 nt fn j tk st@((HappyState (action))) sts stk
     = action nt j tk st ((st):(sts)) (fn `HappyStk` stk)

happySpecReduce_1 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_1 nt fn j tk _ sts@(((st@(HappyState (action))):(_))) (v1`HappyStk`stk')
     = let r = fn v1 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_2 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_2 nt fn j tk _ ((_):(sts@(((st@(HappyState (action))):(_))))) (v1`HappyStk`v2`HappyStk`stk')
     = let r = fn v1 v2 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happySpecReduce_3 i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happySpecReduce_3 nt fn j tk _ ((_):(((_):(sts@(((st@(HappyState (action))):(_))))))) (v1`HappyStk`v2`HappyStk`v3`HappyStk`stk')
     = let r = fn v1 v2 v3 in
       happySeq r (action nt j tk st sts (r `HappyStk` stk'))

happyReduce k i fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyReduce k nt fn j tk st sts stk
     = case happyDrop (k Prelude.- ((1) :: Prelude.Int)) sts of
         sts1@(((st1@(HappyState (action))):(_))) ->
                let r = fn stk in  -- it doesn't hurt to always seq here...
                happyDoSeq r (action nt j tk st1 sts1 r)

happyMonadReduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonadReduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
          let drop_stk = happyDropStk k stk in
          happyThen1 (fn stk tk) (\r -> action nt j tk st1 sts1 (r `HappyStk` drop_stk))

happyMonad2Reduce k nt fn (1) tk st sts stk
     = happyFail [] (1) tk st sts stk
happyMonad2Reduce k nt fn j tk st sts stk =
      case happyDrop k ((st):(sts)) of
        sts1@(((st1@(HappyState (action))):(_))) ->
         let drop_stk = happyDropStk k stk





             _ = nt :: Prelude.Int
             new_state = action

          in
          happyThen1 (fn stk tk) (\r -> happyNewToken new_state sts1 (r `HappyStk` drop_stk))

happyDrop (0) l = l
happyDrop n ((_):(t)) = happyDrop (n Prelude.- ((1) :: Prelude.Int)) t

happyDropStk (0) l = l
happyDropStk n (x `HappyStk` xs) = happyDropStk (n Prelude.- ((1)::Prelude.Int)) xs

-----------------------------------------------------------------------------
-- Moving to a new state after a reduction









happyGoto action j tk st = action j j tk (HappyState action)


-----------------------------------------------------------------------------
-- Error recovery (ERROR_TOK is the error token)

-- parse error if we are in recovery and we fail again
happyFail explist (1) tk old_st _ stk@(x `HappyStk` _) =
     let i = (case x of { HappyErrorToken (i) -> i }) in
--      trace "failing" $ 
        happyError_ explist i tk

{-  We don't need state discarding for our restricted implementation of
    "error".  In fact, it can cause some bogus parses, so I've disabled it
    for now --SDM

-- discard a state
happyFail  ERROR_TOK tk old_st CONS(HAPPYSTATE(action),sts) 
                                                (saved_tok `HappyStk` _ `HappyStk` stk) =
--      trace ("discarding state, depth " ++ show (length stk))  $
        DO_ACTION(action,ERROR_TOK,tk,sts,(saved_tok`HappyStk`stk))
-}

-- Enter error recovery: generate an error token,
--                       save the old token and carry on.
happyFail explist i tk (HappyState (action)) sts stk =
--      trace "entering error recovery" $
        action (1) (1) tk (HappyState (action)) sts ((HappyErrorToken (i)) `HappyStk` stk)

-- Internal happy errors:

notHappyAtAll :: a
notHappyAtAll = Prelude.error "Internal Happy error\n"

-----------------------------------------------------------------------------
-- Hack to get the typechecker to accept our action functions







-----------------------------------------------------------------------------
-- Seq-ing.  If the --strict flag is given, then Happy emits 
--      happySeq = happyDoSeq
-- otherwise it emits
--      happySeq = happyDontSeq

happyDoSeq, happyDontSeq :: a -> b -> b
happyDoSeq   a b = a `Prelude.seq` b
happyDontSeq a b = b

-----------------------------------------------------------------------------
-- Don't inline any functions from the template.  GHC has a nasty habit
-- of deciding to inline happyGoto everywhere, which increases the size of
-- the generated parser quite a bit.









{-# NOINLINE happyShift #-}
{-# NOINLINE happySpecReduce_0 #-}
{-# NOINLINE happySpecReduce_1 #-}
{-# NOINLINE happySpecReduce_2 #-}
{-# NOINLINE happySpecReduce_3 #-}
{-# NOINLINE happyReduce #-}
{-# NOINLINE happyMonadReduce #-}
{-# NOINLINE happyGoto #-}
{-# NOINLINE happyFail #-}

-- end of Happy Template.
