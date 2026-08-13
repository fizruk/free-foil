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
	| HappyAbsSyn19 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn20 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn21 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Module]))
	| HappyAbsSyn22 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn23 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Param))
	| HappyAbsSyn24 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Param]))
	| HappyAbsSyn25 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn26 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn28 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn29 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Discharge))
	| HappyAbsSyn30 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.VarIdent]))
	| HappyAbsSyn31 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn34 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn35 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

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
 action_171 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
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
 happyReduce_65 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,361) ([0,0,0,8,0,0,0,4096,0,0,0,0,32,0,0,16384,0,0,0,0,128,0,0,0,0,8192,0,0,0,0,64,0,0,0,28672,88,0,0,0,45280,0,0,0,0,128,0,0,0,0,0,2,0,24640,6176,1854,0,32768,192,24624,14,0,33024,24577,7360,0,0,770,61633,57,0,1024,8,16384,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128,1,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,12,60963,0,0,0,0,0,0,0,0,0,0,0,24640,6176,1854,0,32768,0,0,0,0,256,0,0,0,0,1026,0,32,0,1024,0,0,0,0,0,0,0,0,4096,0,0,0,0,32,0,0,0,16384,128,0,4,0,49280,12288,3680,0,0,385,49248,28,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6160,1536,460,0,0,0,0,0,0,256,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,32768,0,0,0,0,0,0,0,0,4096,2072,53126,1,0,12320,3088,927,0,0,0,0,4,0,0,0,2048,0,0,0,0,16,0,0,32,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,32768,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,8,0,0,0,0,0,0,0,256,0,0,0,8192,0,0,0,0,0,0,0,32768,0,0,0,0,32768,707,0,0,0,0,0,4,0,0,0,2048,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4096,0,0,8208,0,256,0,8192,64,0,2,0,24640,6176,1854,0,0,32,0,0,0,33024,24705,7416,0,0,770,61633,57,0,14336,0,0,0,0,3080,49924,231,0,4096,2072,53126,1,0,128,0,0,0,16384,128,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1540,57730,115,0,2048,1036,59331,0,0,64,0,0,0,32768,0,0,0,0,24640,6176,1854,0,0,1,0,0,0,2048,0,0,0,0,16,0,0,0,1024,33286,29665,0,0,0,0,0,0,8192,0,0,0,0,0,0,0,0,16384,8288,15896,7,0,1024,0,0,0,0,0,256,0,0,0,4096,0,0,0,0,0,0,0,2048,1036,59331,0,0,512,0,0,0,0,1024,0,0,0,128,0,0,0,0,4,0,0,0,0,5660,0,0,0,770,61633,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12320,3088,927,0,16384,8288,15896,7,0,0,0,0,0,0,16384,0,0,0,512,49411,14832,0,0,1540,57730,115,0,4096,0,0,0,0,32,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,4096,0,0,0,0,3080,49924,231,0,8192,0,0,0,0,64,0,0,0,0,4,0,0,0,0,0,1,0,0,33153,63584,28,0,0,0,0,0,0,28672,88,0,0,0,0,0,0,0,256,0,0,0,0,0,0,0,0,24640,6176,1854,0,0,0,512,0,0,0,0,256,0,0,0,0,0,0,1024,33286,29665,0,0,3080,49924,231,0,8192,0,0,0,0,64,0,0,0,16384,8288,15896,7,0,49280,12352,3708,0,0,0,0,0,0,512,49411,14832,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListModule_internal","%start_pModule_internal","%start_pParam_internal","%start_pListParam_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pDischarge_internal","%start_pListVarIdent_internal","%start_pTerm_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListModule","Module","Param","ListParam","Import","ListImport","Decl","ListDecl","Discharge","ListVarIdent","Term","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'let'","'module'","'namespace'","'open'","'over'","'private'","'refl'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\8658'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 73
        bit_end = (st Prelude.+ 1) Prelude.* 73
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..72]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (52) = happyShift action_65
action_0 (20) = happyGoto action_68
action_0 (21) = happyGoto action_69
action_0 (22) = happyGoto action_67
action_0 _ = happyReduce_18

action_1 (52) = happyShift action_65
action_1 (21) = happyGoto action_66
action_1 (22) = happyGoto action_67
action_1 _ = happyReduce_18

action_2 (52) = happyShift action_65
action_2 (22) = happyGoto action_64
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (36) = happyShift action_62
action_3 (23) = happyGoto action_63
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (36) = happyShift action_62
action_4 (23) = happyGoto action_60
action_4 (24) = happyGoto action_61
action_4 _ = happyReduce_22

action_5 (49) = happyShift action_58
action_5 (25) = happyGoto action_59
action_5 _ = happyFail (happyExpListPerState 5)

action_6 (49) = happyShift action_58
action_6 (25) = happyGoto action_56
action_6 (26) = happyGoto action_57
action_6 _ = happyReduce_25

action_7 (46) = happyShift action_49
action_7 (47) = happyShift action_50
action_7 (48) = happyShift action_51
action_7 (53) = happyShift action_52
action_7 (54) = happyShift action_53
action_7 (56) = happyShift action_54
action_7 (27) = happyGoto action_55
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (46) = happyShift action_49
action_8 (47) = happyShift action_50
action_8 (48) = happyShift action_51
action_8 (53) = happyShift action_52
action_8 (54) = happyShift action_53
action_8 (56) = happyShift action_54
action_8 (27) = happyGoto action_47
action_8 (28) = happyGoto action_48
action_8 _ = happyReduce_33

action_9 (55) = happyShift action_46
action_9 (29) = happyGoto action_45
action_9 _ = happyReduce_36

action_10 (72) = happyShift action_17
action_10 (19) = happyGoto action_43
action_10 (30) = happyGoto action_44
action_10 _ = happyReduce_38

action_11 (36) = happyShift action_27
action_11 (43) = happyShift action_28
action_11 (44) = happyShift action_29
action_11 (51) = happyShift action_30
action_11 (57) = happyShift action_31
action_11 (58) = happyShift action_32
action_11 (63) = happyShift action_33
action_11 (64) = happyShift action_34
action_11 (65) = happyShift action_35
action_11 (66) = happyShift action_36
action_11 (67) = happyShift action_37
action_11 (70) = happyShift action_38
action_11 (71) = happyShift action_39
action_11 (72) = happyShift action_17
action_11 (19) = happyGoto action_22
action_11 (31) = happyGoto action_42
action_11 (32) = happyGoto action_24
action_11 (33) = happyGoto action_25
action_11 _ = happyFail (happyExpListPerState 11)

action_12 (36) = happyShift action_27
action_12 (43) = happyShift action_28
action_12 (44) = happyShift action_29
action_12 (57) = happyShift action_31
action_12 (58) = happyShift action_32
action_12 (66) = happyShift action_36
action_12 (67) = happyShift action_37
action_12 (70) = happyShift action_38
action_12 (71) = happyShift action_39
action_12 (72) = happyShift action_17
action_12 (19) = happyGoto action_22
action_12 (32) = happyGoto action_41
action_12 (33) = happyGoto action_25
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (36) = happyShift action_27
action_13 (43) = happyShift action_28
action_13 (44) = happyShift action_29
action_13 (57) = happyShift action_31
action_13 (58) = happyShift action_32
action_13 (66) = happyShift action_36
action_13 (67) = happyShift action_37
action_13 (70) = happyShift action_38
action_13 (71) = happyShift action_39
action_13 (72) = happyShift action_17
action_13 (19) = happyGoto action_22
action_13 (33) = happyGoto action_40
action_13 _ = happyFail (happyExpListPerState 13)

action_14 (36) = happyShift action_27
action_14 (43) = happyShift action_28
action_14 (44) = happyShift action_29
action_14 (51) = happyShift action_30
action_14 (57) = happyShift action_31
action_14 (58) = happyShift action_32
action_14 (63) = happyShift action_33
action_14 (64) = happyShift action_34
action_14 (65) = happyShift action_35
action_14 (66) = happyShift action_36
action_14 (67) = happyShift action_37
action_14 (70) = happyShift action_38
action_14 (71) = happyShift action_39
action_14 (72) = happyShift action_17
action_14 (19) = happyGoto action_22
action_14 (31) = happyGoto action_23
action_14 (32) = happyGoto action_24
action_14 (33) = happyGoto action_25
action_14 (34) = happyGoto action_26
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (36) = happyShift action_20
action_15 (45) = happyShift action_21
action_15 (72) = happyShift action_17
action_15 (19) = happyGoto action_18
action_15 (35) = happyGoto action_19
action_15 _ = happyFail (happyExpListPerState 15)

action_16 (72) = happyShift action_17
action_16 _ = happyFail (happyExpListPerState 16)

action_17 _ = happyReduce_16

action_18 _ = happyReduce_64

action_19 (73) = happyAccept
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (36) = happyShift action_20
action_20 (45) = happyShift action_21
action_20 (72) = happyShift action_17
action_20 (19) = happyGoto action_18
action_20 (35) = happyGoto action_98
action_20 _ = happyFail (happyExpListPerState 20)

action_21 _ = happyReduce_63

action_22 _ = happyReduce_55

action_23 _ = happyReduce_62

action_24 (36) = happyShift action_27
action_24 (43) = happyShift action_28
action_24 (44) = happyShift action_29
action_24 (57) = happyShift action_31
action_24 (58) = happyShift action_32
action_24 (62) = happyShift action_96
action_24 (66) = happyShift action_36
action_24 (67) = happyShift action_37
action_24 (68) = happyShift action_97
action_24 (70) = happyShift action_38
action_24 (71) = happyShift action_39
action_24 (72) = happyShift action_17
action_24 (19) = happyGoto action_22
action_24 (33) = happyGoto action_85
action_24 _ = happyReduce_47

action_25 _ = happyReduce_49

action_26 (73) = happyAccept
action_26 _ = happyFail (happyExpListPerState 26)

action_27 (36) = happyShift action_27
action_27 (43) = happyShift action_28
action_27 (44) = happyShift action_29
action_27 (51) = happyShift action_30
action_27 (57) = happyShift action_31
action_27 (58) = happyShift action_32
action_27 (63) = happyShift action_33
action_27 (64) = happyShift action_34
action_27 (65) = happyShift action_35
action_27 (66) = happyShift action_36
action_27 (67) = happyShift action_37
action_27 (70) = happyShift action_38
action_27 (71) = happyShift action_39
action_27 (72) = happyShift action_17
action_27 (19) = happyGoto action_22
action_27 (31) = happyGoto action_95
action_27 (32) = happyGoto action_24
action_27 (33) = happyGoto action_25
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (36) = happyShift action_94
action_28 _ = happyFail (happyExpListPerState 28)

action_29 (36) = happyShift action_93
action_29 _ = happyFail (happyExpListPerState 29)

action_30 (36) = happyShift action_20
action_30 (45) = happyShift action_21
action_30 (72) = happyShift action_17
action_30 (19) = happyGoto action_18
action_30 (35) = happyGoto action_92
action_30 _ = happyFail (happyExpListPerState 30)

action_31 (36) = happyShift action_91
action_31 _ = happyFail (happyExpListPerState 31)

action_32 _ = happyReduce_54

action_33 (36) = happyShift action_90
action_33 _ = happyFail (happyExpListPerState 33)

action_34 (36) = happyShift action_89
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (36) = happyShift action_20
action_35 (45) = happyShift action_21
action_35 (72) = happyShift action_17
action_35 (19) = happyGoto action_18
action_35 (35) = happyGoto action_88
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (36) = happyShift action_27
action_36 (43) = happyShift action_28
action_36 (44) = happyShift action_29
action_36 (57) = happyShift action_31
action_36 (58) = happyShift action_32
action_36 (66) = happyShift action_36
action_36 (67) = happyShift action_37
action_36 (70) = happyShift action_38
action_36 (71) = happyShift action_39
action_36 (72) = happyShift action_17
action_36 (19) = happyGoto action_22
action_36 (33) = happyGoto action_87
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (36) = happyShift action_27
action_37 (43) = happyShift action_28
action_37 (44) = happyShift action_29
action_37 (57) = happyShift action_31
action_37 (58) = happyShift action_32
action_37 (66) = happyShift action_36
action_37 (67) = happyShift action_37
action_37 (70) = happyShift action_38
action_37 (71) = happyShift action_39
action_37 (72) = happyShift action_17
action_37 (19) = happyGoto action_22
action_37 (33) = happyGoto action_86
action_37 _ = happyFail (happyExpListPerState 37)

action_38 _ = happyReduce_52

action_39 _ = happyReduce_53

action_40 (73) = happyAccept
action_40 _ = happyFail (happyExpListPerState 40)

action_41 (36) = happyShift action_27
action_41 (43) = happyShift action_28
action_41 (44) = happyShift action_29
action_41 (57) = happyShift action_31
action_41 (58) = happyShift action_32
action_41 (66) = happyShift action_36
action_41 (67) = happyShift action_37
action_41 (70) = happyShift action_38
action_41 (71) = happyShift action_39
action_41 (72) = happyShift action_17
action_41 (73) = happyAccept
action_41 (19) = happyGoto action_22
action_41 (33) = happyGoto action_85
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (73) = happyAccept
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (38) = happyShift action_84
action_43 _ = happyReduce_39

action_44 (73) = happyAccept
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (73) = happyAccept
action_45 _ = happyFail (happyExpListPerState 45)

action_46 (36) = happyShift action_83
action_46 _ = happyFail (happyExpListPerState 46)

action_47 (41) = happyShift action_82
action_47 _ = happyReduce_34

action_48 (73) = happyAccept
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (36) = happyShift action_27
action_49 (43) = happyShift action_28
action_49 (44) = happyShift action_29
action_49 (51) = happyShift action_30
action_49 (57) = happyShift action_31
action_49 (58) = happyShift action_32
action_49 (63) = happyShift action_33
action_49 (64) = happyShift action_34
action_49 (65) = happyShift action_35
action_49 (66) = happyShift action_36
action_49 (67) = happyShift action_37
action_49 (70) = happyShift action_38
action_49 (71) = happyShift action_39
action_49 (72) = happyShift action_17
action_49 (19) = happyGoto action_22
action_49 (31) = happyGoto action_81
action_49 (32) = happyGoto action_24
action_49 (33) = happyGoto action_25
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (36) = happyShift action_27
action_50 (43) = happyShift action_28
action_50 (44) = happyShift action_29
action_50 (51) = happyShift action_30
action_50 (57) = happyShift action_31
action_50 (58) = happyShift action_32
action_50 (63) = happyShift action_33
action_50 (64) = happyShift action_34
action_50 (65) = happyShift action_35
action_50 (66) = happyShift action_36
action_50 (67) = happyShift action_37
action_50 (70) = happyShift action_38
action_50 (71) = happyShift action_39
action_50 (72) = happyShift action_17
action_50 (19) = happyGoto action_22
action_50 (31) = happyGoto action_80
action_50 (32) = happyGoto action_24
action_50 (33) = happyGoto action_25
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (72) = happyShift action_17
action_51 (19) = happyGoto action_79
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (72) = happyShift action_17
action_52 (19) = happyGoto action_78
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (72) = happyShift action_17
action_53 (19) = happyGoto action_77
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (48) = happyShift action_76
action_54 _ = happyFail (happyExpListPerState 54)

action_55 (73) = happyAccept
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (41) = happyShift action_75
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (73) = happyAccept
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (72) = happyShift action_17
action_58 (19) = happyGoto action_74
action_58 _ = happyFail (happyExpListPerState 58)

action_59 (73) = happyAccept
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (36) = happyShift action_62
action_60 (23) = happyGoto action_60
action_60 (24) = happyGoto action_73
action_60 _ = happyReduce_22

action_61 (73) = happyAccept
action_61 _ = happyFail (happyExpListPerState 61)

action_62 (72) = happyShift action_17
action_62 (19) = happyGoto action_72
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (73) = happyAccept
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (73) = happyAccept
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (72) = happyShift action_17
action_65 (19) = happyGoto action_71
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (73) = happyAccept
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (52) = happyShift action_65
action_67 (21) = happyGoto action_70
action_67 (22) = happyGoto action_67
action_67 _ = happyReduce_18

action_68 (73) = happyAccept
action_68 _ = happyFail (happyExpListPerState 68)

action_69 _ = happyReduce_17

action_70 _ = happyReduce_19

action_71 (36) = happyShift action_62
action_71 (23) = happyGoto action_60
action_71 (24) = happyGoto action_121
action_71 _ = happyReduce_22

action_72 (39) = happyShift action_120
action_72 _ = happyFail (happyExpListPerState 72)

action_73 _ = happyReduce_23

action_74 _ = happyReduce_24

action_75 (49) = happyShift action_58
action_75 (25) = happyGoto action_56
action_75 (26) = happyGoto action_119
action_75 _ = happyReduce_25

action_76 (72) = happyShift action_17
action_76 (19) = happyGoto action_118
action_76 _ = happyFail (happyExpListPerState 76)

action_77 _ = happyReduce_30

action_78 (59) = happyShift action_117
action_78 _ = happyFail (happyExpListPerState 78)

action_79 (55) = happyShift action_46
action_79 (29) = happyGoto action_116
action_79 _ = happyReduce_36

action_80 _ = happyReduce_32

action_81 (39) = happyShift action_115
action_81 _ = happyFail (happyExpListPerState 81)

action_82 (46) = happyShift action_49
action_82 (47) = happyShift action_50
action_82 (48) = happyShift action_51
action_82 (53) = happyShift action_52
action_82 (54) = happyShift action_53
action_82 (56) = happyShift action_54
action_82 (27) = happyGoto action_47
action_82 (28) = happyGoto action_114
action_82 _ = happyReduce_33

action_83 (72) = happyShift action_17
action_83 (19) = happyGoto action_43
action_83 (30) = happyGoto action_113
action_83 _ = happyReduce_38

action_84 (72) = happyShift action_17
action_84 (19) = happyGoto action_43
action_84 (30) = happyGoto action_112
action_84 _ = happyReduce_38

action_85 _ = happyReduce_48

action_86 _ = happyReduce_51

action_87 _ = happyReduce_50

action_88 (69) = happyShift action_111
action_88 _ = happyFail (happyExpListPerState 88)

action_89 (36) = happyShift action_20
action_89 (45) = happyShift action_21
action_89 (72) = happyShift action_17
action_89 (19) = happyGoto action_18
action_89 (35) = happyGoto action_110
action_89 _ = happyFail (happyExpListPerState 89)

action_90 (36) = happyShift action_20
action_90 (45) = happyShift action_21
action_90 (72) = happyShift action_17
action_90 (19) = happyGoto action_18
action_90 (35) = happyGoto action_109
action_90 _ = happyFail (happyExpListPerState 90)

action_91 (36) = happyShift action_27
action_91 (43) = happyShift action_28
action_91 (44) = happyShift action_29
action_91 (51) = happyShift action_30
action_91 (57) = happyShift action_31
action_91 (58) = happyShift action_32
action_91 (63) = happyShift action_33
action_91 (64) = happyShift action_34
action_91 (65) = happyShift action_35
action_91 (66) = happyShift action_36
action_91 (67) = happyShift action_37
action_91 (70) = happyShift action_38
action_91 (71) = happyShift action_39
action_91 (72) = happyShift action_17
action_91 (19) = happyGoto action_22
action_91 (31) = happyGoto action_108
action_91 (32) = happyGoto action_24
action_91 (33) = happyGoto action_25
action_91 _ = happyFail (happyExpListPerState 91)

action_92 (42) = happyShift action_107
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (36) = happyShift action_27
action_93 (43) = happyShift action_28
action_93 (44) = happyShift action_29
action_93 (51) = happyShift action_30
action_93 (57) = happyShift action_31
action_93 (58) = happyShift action_32
action_93 (63) = happyShift action_33
action_93 (64) = happyShift action_34
action_93 (65) = happyShift action_35
action_93 (66) = happyShift action_36
action_93 (67) = happyShift action_37
action_93 (70) = happyShift action_38
action_93 (71) = happyShift action_39
action_93 (72) = happyShift action_17
action_93 (19) = happyGoto action_22
action_93 (31) = happyGoto action_106
action_93 (32) = happyGoto action_24
action_93 (33) = happyGoto action_25
action_93 _ = happyFail (happyExpListPerState 93)

action_94 (36) = happyShift action_27
action_94 (43) = happyShift action_28
action_94 (44) = happyShift action_29
action_94 (51) = happyShift action_30
action_94 (57) = happyShift action_31
action_94 (58) = happyShift action_32
action_94 (63) = happyShift action_33
action_94 (64) = happyShift action_34
action_94 (65) = happyShift action_35
action_94 (66) = happyShift action_36
action_94 (67) = happyShift action_37
action_94 (70) = happyShift action_38
action_94 (71) = happyShift action_39
action_94 (72) = happyShift action_17
action_94 (19) = happyGoto action_22
action_94 (31) = happyGoto action_105
action_94 (32) = happyGoto action_24
action_94 (33) = happyGoto action_25
action_94 _ = happyFail (happyExpListPerState 94)

action_95 (37) = happyShift action_102
action_95 (38) = happyShift action_103
action_95 (39) = happyShift action_104
action_95 _ = happyFail (happyExpListPerState 95)

action_96 (36) = happyShift action_27
action_96 (43) = happyShift action_28
action_96 (44) = happyShift action_29
action_96 (51) = happyShift action_30
action_96 (57) = happyShift action_31
action_96 (58) = happyShift action_32
action_96 (63) = happyShift action_33
action_96 (64) = happyShift action_34
action_96 (65) = happyShift action_35
action_96 (66) = happyShift action_36
action_96 (67) = happyShift action_37
action_96 (70) = happyShift action_38
action_96 (71) = happyShift action_39
action_96 (72) = happyShift action_17
action_96 (19) = happyGoto action_22
action_96 (31) = happyGoto action_101
action_96 (32) = happyGoto action_24
action_96 (33) = happyGoto action_25
action_96 _ = happyFail (happyExpListPerState 96)

action_97 (36) = happyShift action_27
action_97 (43) = happyShift action_28
action_97 (44) = happyShift action_29
action_97 (51) = happyShift action_30
action_97 (57) = happyShift action_31
action_97 (58) = happyShift action_32
action_97 (63) = happyShift action_33
action_97 (64) = happyShift action_34
action_97 (65) = happyShift action_35
action_97 (66) = happyShift action_36
action_97 (67) = happyShift action_37
action_97 (70) = happyShift action_38
action_97 (71) = happyShift action_39
action_97 (72) = happyShift action_17
action_97 (19) = happyGoto action_22
action_97 (31) = happyGoto action_100
action_97 (32) = happyGoto action_24
action_97 (33) = happyGoto action_25
action_97 _ = happyFail (happyExpListPerState 97)

action_98 (38) = happyShift action_99
action_98 _ = happyFail (happyExpListPerState 98)

action_99 (36) = happyShift action_20
action_99 (45) = happyShift action_21
action_99 (72) = happyShift action_17
action_99 (19) = happyGoto action_18
action_99 (35) = happyGoto action_138
action_99 _ = happyFail (happyExpListPerState 99)

action_100 _ = happyReduce_45

action_101 _ = happyReduce_46

action_102 _ = happyReduce_61

action_103 (36) = happyShift action_27
action_103 (43) = happyShift action_28
action_103 (44) = happyShift action_29
action_103 (51) = happyShift action_30
action_103 (57) = happyShift action_31
action_103 (58) = happyShift action_32
action_103 (63) = happyShift action_33
action_103 (64) = happyShift action_34
action_103 (65) = happyShift action_35
action_103 (66) = happyShift action_36
action_103 (67) = happyShift action_37
action_103 (70) = happyShift action_38
action_103 (71) = happyShift action_39
action_103 (72) = happyShift action_17
action_103 (19) = happyGoto action_22
action_103 (31) = happyGoto action_137
action_103 (32) = happyGoto action_24
action_103 (33) = happyGoto action_25
action_103 _ = happyFail (happyExpListPerState 103)

action_104 (36) = happyShift action_27
action_104 (43) = happyShift action_28
action_104 (44) = happyShift action_29
action_104 (51) = happyShift action_30
action_104 (57) = happyShift action_31
action_104 (58) = happyShift action_32
action_104 (63) = happyShift action_33
action_104 (64) = happyShift action_34
action_104 (65) = happyShift action_35
action_104 (66) = happyShift action_36
action_104 (67) = happyShift action_37
action_104 (70) = happyShift action_38
action_104 (71) = happyShift action_39
action_104 (72) = happyShift action_17
action_104 (19) = happyGoto action_22
action_104 (31) = happyGoto action_136
action_104 (32) = happyGoto action_24
action_104 (33) = happyGoto action_25
action_104 _ = happyFail (happyExpListPerState 104)

action_105 (38) = happyShift action_135
action_105 _ = happyFail (happyExpListPerState 105)

action_106 (38) = happyShift action_134
action_106 _ = happyFail (happyExpListPerState 106)

action_107 (36) = happyShift action_27
action_107 (43) = happyShift action_28
action_107 (44) = happyShift action_29
action_107 (51) = happyShift action_30
action_107 (57) = happyShift action_31
action_107 (58) = happyShift action_32
action_107 (63) = happyShift action_33
action_107 (64) = happyShift action_34
action_107 (65) = happyShift action_35
action_107 (66) = happyShift action_36
action_107 (67) = happyShift action_37
action_107 (70) = happyShift action_38
action_107 (71) = happyShift action_39
action_107 (72) = happyShift action_17
action_107 (19) = happyGoto action_22
action_107 (31) = happyGoto action_133
action_107 (32) = happyGoto action_24
action_107 (33) = happyGoto action_25
action_107 _ = happyFail (happyExpListPerState 107)

action_108 (37) = happyShift action_132
action_108 _ = happyFail (happyExpListPerState 108)

action_109 (39) = happyShift action_131
action_109 _ = happyFail (happyExpListPerState 109)

action_110 (39) = happyShift action_130
action_110 _ = happyFail (happyExpListPerState 110)

action_111 (36) = happyShift action_27
action_111 (43) = happyShift action_28
action_111 (44) = happyShift action_29
action_111 (51) = happyShift action_30
action_111 (57) = happyShift action_31
action_111 (58) = happyShift action_32
action_111 (63) = happyShift action_33
action_111 (64) = happyShift action_34
action_111 (65) = happyShift action_35
action_111 (66) = happyShift action_36
action_111 (67) = happyShift action_37
action_111 (70) = happyShift action_38
action_111 (71) = happyShift action_39
action_111 (72) = happyShift action_17
action_111 (19) = happyGoto action_22
action_111 (31) = happyGoto action_23
action_111 (32) = happyGoto action_24
action_111 (33) = happyGoto action_25
action_111 (34) = happyGoto action_129
action_111 _ = happyFail (happyExpListPerState 111)

action_112 _ = happyReduce_40

action_113 (37) = happyShift action_128
action_113 _ = happyFail (happyExpListPerState 113)

action_114 _ = happyReduce_35

action_115 (36) = happyShift action_27
action_115 (43) = happyShift action_28
action_115 (44) = happyShift action_29
action_115 (51) = happyShift action_30
action_115 (57) = happyShift action_31
action_115 (58) = happyShift action_32
action_115 (63) = happyShift action_33
action_115 (64) = happyShift action_34
action_115 (65) = happyShift action_35
action_115 (66) = happyShift action_36
action_115 (67) = happyShift action_37
action_115 (70) = happyShift action_38
action_115 (71) = happyShift action_39
action_115 (72) = happyShift action_17
action_115 (19) = happyGoto action_22
action_115 (31) = happyGoto action_127
action_115 (32) = happyGoto action_24
action_115 (33) = happyGoto action_25
action_115 _ = happyFail (happyExpListPerState 115)

action_116 (39) = happyShift action_126
action_116 _ = happyFail (happyExpListPerState 116)

action_117 (60) = happyShift action_125
action_117 _ = happyFail (happyExpListPerState 117)

action_118 (55) = happyShift action_46
action_118 (29) = happyGoto action_124
action_118 _ = happyReduce_36

action_119 _ = happyReduce_26

action_120 (36) = happyShift action_27
action_120 (43) = happyShift action_28
action_120 (44) = happyShift action_29
action_120 (51) = happyShift action_30
action_120 (57) = happyShift action_31
action_120 (58) = happyShift action_32
action_120 (63) = happyShift action_33
action_120 (64) = happyShift action_34
action_120 (65) = happyShift action_35
action_120 (66) = happyShift action_36
action_120 (67) = happyShift action_37
action_120 (70) = happyShift action_38
action_120 (71) = happyShift action_39
action_120 (72) = happyShift action_17
action_120 (19) = happyGoto action_22
action_120 (31) = happyGoto action_123
action_120 (32) = happyGoto action_24
action_120 (33) = happyGoto action_25
action_120 _ = happyFail (happyExpListPerState 120)

action_121 (41) = happyShift action_122
action_121 _ = happyFail (happyExpListPerState 121)

action_122 (49) = happyShift action_58
action_122 (25) = happyGoto action_56
action_122 (26) = happyGoto action_151
action_122 _ = happyReduce_25

action_123 (37) = happyShift action_150
action_123 _ = happyFail (happyExpListPerState 123)

action_124 (39) = happyShift action_149
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (46) = happyShift action_49
action_125 (47) = happyShift action_50
action_125 (48) = happyShift action_51
action_125 (53) = happyShift action_52
action_125 (54) = happyShift action_53
action_125 (56) = happyShift action_54
action_125 (27) = happyGoto action_47
action_125 (28) = happyGoto action_148
action_125 _ = happyReduce_33

action_126 (36) = happyShift action_27
action_126 (43) = happyShift action_28
action_126 (44) = happyShift action_29
action_126 (51) = happyShift action_30
action_126 (57) = happyShift action_31
action_126 (58) = happyShift action_32
action_126 (63) = happyShift action_33
action_126 (64) = happyShift action_34
action_126 (65) = happyShift action_35
action_126 (66) = happyShift action_36
action_126 (67) = happyShift action_37
action_126 (70) = happyShift action_38
action_126 (71) = happyShift action_39
action_126 (72) = happyShift action_17
action_126 (19) = happyGoto action_22
action_126 (31) = happyGoto action_147
action_126 (32) = happyGoto action_24
action_126 (33) = happyGoto action_25
action_126 _ = happyFail (happyExpListPerState 126)

action_127 _ = happyReduce_31

action_128 _ = happyReduce_37

action_129 _ = happyReduce_43

action_130 (36) = happyShift action_27
action_130 (43) = happyShift action_28
action_130 (44) = happyShift action_29
action_130 (51) = happyShift action_30
action_130 (57) = happyShift action_31
action_130 (58) = happyShift action_32
action_130 (63) = happyShift action_33
action_130 (64) = happyShift action_34
action_130 (65) = happyShift action_35
action_130 (66) = happyShift action_36
action_130 (67) = happyShift action_37
action_130 (70) = happyShift action_38
action_130 (71) = happyShift action_39
action_130 (72) = happyShift action_17
action_130 (19) = happyGoto action_22
action_130 (31) = happyGoto action_146
action_130 (32) = happyGoto action_24
action_130 (33) = happyGoto action_25
action_130 _ = happyFail (happyExpListPerState 130)

action_131 (36) = happyShift action_27
action_131 (43) = happyShift action_28
action_131 (44) = happyShift action_29
action_131 (51) = happyShift action_30
action_131 (57) = happyShift action_31
action_131 (58) = happyShift action_32
action_131 (63) = happyShift action_33
action_131 (64) = happyShift action_34
action_131 (65) = happyShift action_35
action_131 (66) = happyShift action_36
action_131 (67) = happyShift action_37
action_131 (70) = happyShift action_38
action_131 (71) = happyShift action_39
action_131 (72) = happyShift action_17
action_131 (19) = happyGoto action_22
action_131 (31) = happyGoto action_145
action_131 (32) = happyGoto action_24
action_131 (33) = happyGoto action_25
action_131 _ = happyFail (happyExpListPerState 131)

action_132 _ = happyReduce_57

action_133 (50) = happyShift action_144
action_133 _ = happyFail (happyExpListPerState 133)

action_134 (36) = happyShift action_27
action_134 (43) = happyShift action_28
action_134 (44) = happyShift action_29
action_134 (51) = happyShift action_30
action_134 (57) = happyShift action_31
action_134 (58) = happyShift action_32
action_134 (63) = happyShift action_33
action_134 (64) = happyShift action_34
action_134 (65) = happyShift action_35
action_134 (66) = happyShift action_36
action_134 (67) = happyShift action_37
action_134 (70) = happyShift action_38
action_134 (71) = happyShift action_39
action_134 (72) = happyShift action_17
action_134 (19) = happyGoto action_22
action_134 (31) = happyGoto action_143
action_134 (32) = happyGoto action_24
action_134 (33) = happyGoto action_25
action_134 _ = happyFail (happyExpListPerState 134)

action_135 (36) = happyShift action_27
action_135 (43) = happyShift action_28
action_135 (44) = happyShift action_29
action_135 (51) = happyShift action_30
action_135 (57) = happyShift action_31
action_135 (58) = happyShift action_32
action_135 (63) = happyShift action_33
action_135 (64) = happyShift action_34
action_135 (65) = happyShift action_35
action_135 (66) = happyShift action_36
action_135 (67) = happyShift action_37
action_135 (70) = happyShift action_38
action_135 (71) = happyShift action_39
action_135 (72) = happyShift action_17
action_135 (19) = happyGoto action_22
action_135 (31) = happyGoto action_142
action_135 (32) = happyGoto action_24
action_135 (33) = happyGoto action_25
action_135 _ = happyFail (happyExpListPerState 135)

action_136 (37) = happyShift action_141
action_136 _ = happyFail (happyExpListPerState 136)

action_137 (37) = happyShift action_140
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (37) = happyShift action_139
action_138 _ = happyFail (happyExpListPerState 138)

action_139 _ = happyReduce_65

action_140 _ = happyReduce_59

action_141 _ = happyReduce_60

action_142 (38) = happyShift action_160
action_142 _ = happyFail (happyExpListPerState 142)

action_143 (38) = happyShift action_159
action_143 _ = happyFail (happyExpListPerState 143)

action_144 (36) = happyShift action_27
action_144 (43) = happyShift action_28
action_144 (44) = happyShift action_29
action_144 (51) = happyShift action_30
action_144 (57) = happyShift action_31
action_144 (58) = happyShift action_32
action_144 (63) = happyShift action_33
action_144 (64) = happyShift action_34
action_144 (65) = happyShift action_35
action_144 (66) = happyShift action_36
action_144 (67) = happyShift action_37
action_144 (70) = happyShift action_38
action_144 (71) = happyShift action_39
action_144 (72) = happyShift action_17
action_144 (19) = happyGoto action_22
action_144 (31) = happyGoto action_23
action_144 (32) = happyGoto action_24
action_144 (33) = happyGoto action_25
action_144 (34) = happyGoto action_158
action_144 _ = happyFail (happyExpListPerState 144)

action_145 (37) = happyShift action_157
action_145 _ = happyFail (happyExpListPerState 145)

action_146 (37) = happyShift action_156
action_146 _ = happyFail (happyExpListPerState 146)

action_147 (40) = happyShift action_155
action_147 _ = happyFail (happyExpListPerState 147)

action_148 (61) = happyShift action_154
action_148 _ = happyFail (happyExpListPerState 148)

action_149 (36) = happyShift action_27
action_149 (43) = happyShift action_28
action_149 (44) = happyShift action_29
action_149 (51) = happyShift action_30
action_149 (57) = happyShift action_31
action_149 (58) = happyShift action_32
action_149 (63) = happyShift action_33
action_149 (64) = happyShift action_34
action_149 (65) = happyShift action_35
action_149 (66) = happyShift action_36
action_149 (67) = happyShift action_37
action_149 (70) = happyShift action_38
action_149 (71) = happyShift action_39
action_149 (72) = happyShift action_17
action_149 (19) = happyGoto action_22
action_149 (31) = happyGoto action_153
action_149 (32) = happyGoto action_24
action_149 (33) = happyGoto action_25
action_149 _ = happyFail (happyExpListPerState 149)

action_150 _ = happyReduce_21

action_151 (46) = happyShift action_49
action_151 (47) = happyShift action_50
action_151 (48) = happyShift action_51
action_151 (53) = happyShift action_52
action_151 (54) = happyShift action_53
action_151 (56) = happyShift action_54
action_151 (27) = happyGoto action_47
action_151 (28) = happyGoto action_152
action_151 _ = happyReduce_33

action_152 _ = happyReduce_20

action_153 (40) = happyShift action_166
action_153 _ = happyFail (happyExpListPerState 153)

action_154 _ = happyReduce_29

action_155 (36) = happyShift action_27
action_155 (43) = happyShift action_28
action_155 (44) = happyShift action_29
action_155 (51) = happyShift action_30
action_155 (57) = happyShift action_31
action_155 (58) = happyShift action_32
action_155 (63) = happyShift action_33
action_155 (64) = happyShift action_34
action_155 (65) = happyShift action_35
action_155 (66) = happyShift action_36
action_155 (67) = happyShift action_37
action_155 (70) = happyShift action_38
action_155 (71) = happyShift action_39
action_155 (72) = happyShift action_17
action_155 (19) = happyGoto action_22
action_155 (31) = happyGoto action_165
action_155 (32) = happyGoto action_24
action_155 (33) = happyGoto action_25
action_155 _ = happyFail (happyExpListPerState 155)

action_156 (62) = happyShift action_164
action_156 _ = happyFail (happyExpListPerState 156)

action_157 (68) = happyShift action_163
action_157 _ = happyFail (happyExpListPerState 157)

action_158 _ = happyReduce_44

action_159 (36) = happyShift action_27
action_159 (43) = happyShift action_28
action_159 (44) = happyShift action_29
action_159 (51) = happyShift action_30
action_159 (57) = happyShift action_31
action_159 (58) = happyShift action_32
action_159 (63) = happyShift action_33
action_159 (64) = happyShift action_34
action_159 (65) = happyShift action_35
action_159 (66) = happyShift action_36
action_159 (67) = happyShift action_37
action_159 (70) = happyShift action_38
action_159 (71) = happyShift action_39
action_159 (72) = happyShift action_17
action_159 (19) = happyGoto action_22
action_159 (31) = happyGoto action_162
action_159 (32) = happyGoto action_24
action_159 (33) = happyGoto action_25
action_159 _ = happyFail (happyExpListPerState 159)

action_160 (36) = happyShift action_27
action_160 (43) = happyShift action_28
action_160 (44) = happyShift action_29
action_160 (51) = happyShift action_30
action_160 (57) = happyShift action_31
action_160 (58) = happyShift action_32
action_160 (63) = happyShift action_33
action_160 (64) = happyShift action_34
action_160 (65) = happyShift action_35
action_160 (66) = happyShift action_36
action_160 (67) = happyShift action_37
action_160 (70) = happyShift action_38
action_160 (71) = happyShift action_39
action_160 (72) = happyShift action_17
action_160 (19) = happyGoto action_22
action_160 (31) = happyGoto action_161
action_160 (32) = happyGoto action_24
action_160 (33) = happyGoto action_25
action_160 _ = happyFail (happyExpListPerState 160)

action_161 (37) = happyShift action_171
action_161 _ = happyFail (happyExpListPerState 161)

action_162 (37) = happyShift action_170
action_162 _ = happyFail (happyExpListPerState 162)

action_163 (36) = happyShift action_27
action_163 (43) = happyShift action_28
action_163 (44) = happyShift action_29
action_163 (51) = happyShift action_30
action_163 (57) = happyShift action_31
action_163 (58) = happyShift action_32
action_163 (63) = happyShift action_33
action_163 (64) = happyShift action_34
action_163 (65) = happyShift action_35
action_163 (66) = happyShift action_36
action_163 (67) = happyShift action_37
action_163 (70) = happyShift action_38
action_163 (71) = happyShift action_39
action_163 (72) = happyShift action_17
action_163 (19) = happyGoto action_22
action_163 (31) = happyGoto action_23
action_163 (32) = happyGoto action_24
action_163 (33) = happyGoto action_25
action_163 (34) = happyGoto action_169
action_163 _ = happyFail (happyExpListPerState 163)

action_164 (36) = happyShift action_27
action_164 (43) = happyShift action_28
action_164 (44) = happyShift action_29
action_164 (51) = happyShift action_30
action_164 (57) = happyShift action_31
action_164 (58) = happyShift action_32
action_164 (63) = happyShift action_33
action_164 (64) = happyShift action_34
action_164 (65) = happyShift action_35
action_164 (66) = happyShift action_36
action_164 (67) = happyShift action_37
action_164 (70) = happyShift action_38
action_164 (71) = happyShift action_39
action_164 (72) = happyShift action_17
action_164 (19) = happyGoto action_22
action_164 (31) = happyGoto action_23
action_164 (32) = happyGoto action_24
action_164 (33) = happyGoto action_25
action_164 (34) = happyGoto action_168
action_164 _ = happyFail (happyExpListPerState 164)

action_165 _ = happyReduce_27

action_166 (36) = happyShift action_27
action_166 (43) = happyShift action_28
action_166 (44) = happyShift action_29
action_166 (51) = happyShift action_30
action_166 (57) = happyShift action_31
action_166 (58) = happyShift action_32
action_166 (63) = happyShift action_33
action_166 (64) = happyShift action_34
action_166 (65) = happyShift action_35
action_166 (66) = happyShift action_36
action_166 (67) = happyShift action_37
action_166 (70) = happyShift action_38
action_166 (71) = happyShift action_39
action_166 (72) = happyShift action_17
action_166 (19) = happyGoto action_22
action_166 (31) = happyGoto action_167
action_166 (32) = happyGoto action_24
action_166 (33) = happyGoto action_25
action_166 _ = happyFail (happyExpListPerState 166)

action_167 _ = happyReduce_28

action_168 _ = happyReduce_42

action_169 _ = happyReduce_41

action_170 _ = happyReduce_58

action_171 _ = happyReduce_56

happyReduce_16 = happySpecReduce_1  19 happyReduction_16
happyReduction_16 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn19
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_16 _  = notHappyAtAll 

happyReduce_17 = happySpecReduce_1  20 happyReduction_17
happyReduction_17 (HappyAbsSyn21  happy_var_1)
	 =  HappyAbsSyn20
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_17 _  = notHappyAtAll 

happyReduce_18 = happySpecReduce_0  21 happyReduction_18
happyReduction_18  =  HappyAbsSyn21
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_19 = happySpecReduce_2  21 happyReduction_19
happyReduction_19 (HappyAbsSyn21  happy_var_2)
	(HappyAbsSyn22  happy_var_1)
	 =  HappyAbsSyn21
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_19 _ _  = notHappyAtAll 

happyReduce_20 = happyReduce 6 22 happyReduction_20
happyReduction_20 ((HappyAbsSyn28  happy_var_6) `HappyStk`
	(HappyAbsSyn26  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn24  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn22
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_21 = happyReduce 5 23 happyReduction_21
happyReduction_21 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn23
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AParam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_22 = happySpecReduce_0  24 happyReduction_22
happyReduction_22  =  HappyAbsSyn24
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_23 = happySpecReduce_2  24 happyReduction_23
happyReduction_23 (HappyAbsSyn24  happy_var_2)
	(HappyAbsSyn23  happy_var_1)
	 =  HappyAbsSyn24
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_23 _ _  = notHappyAtAll 

happyReduce_24 = happySpecReduce_2  25 happyReduction_24
happyReduction_24 (HappyAbsSyn19  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn25
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_24 _ _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_0  26 happyReduction_25
happyReduction_25  =  HappyAbsSyn26
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_26 = happySpecReduce_3  26 happyReduction_26
happyReduction_26 (HappyAbsSyn26  happy_var_3)
	_
	(HappyAbsSyn25  happy_var_1)
	 =  HappyAbsSyn26
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_26 _ _ _  = notHappyAtAll 

happyReduce_27 = happyReduce 7 27 happyReduction_27
happyReduction_27 ((HappyAbsSyn31  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_3) `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_28 = happyReduce 8 27 happyReduction_28
happyReduction_28 ((HappyAbsSyn31  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn29  happy_var_4) `HappyStk`
	(HappyAbsSyn19  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_29 = happyReduce 6 27 happyReduction_29
happyReduction_29 (_ `HappyStk`
	(HappyAbsSyn28  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn19  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_30 = happySpecReduce_2  27 happyReduction_30
happyReduction_30 (HappyAbsSyn19  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_30 _ _  = notHappyAtAll 

happyReduce_31 = happyReduce 4 27 happyReduction_31
happyReduction_31 ((HappyAbsSyn31  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_32 = happySpecReduce_2  27 happyReduction_32
happyReduction_32 (HappyAbsSyn31  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_32 _ _  = notHappyAtAll 

happyReduce_33 = happySpecReduce_0  28 happyReduction_33
happyReduction_33  =  HappyAbsSyn28
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_34 = happySpecReduce_1  28 happyReduction_34
happyReduction_34 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn28
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_34 _  = notHappyAtAll 

happyReduce_35 = happySpecReduce_3  28 happyReduction_35
happyReduction_35 (HappyAbsSyn28  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn28
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_35 _ _ _  = notHappyAtAll 

happyReduce_36 = happySpecReduce_0  29 happyReduction_36
happyReduction_36  =  HappyAbsSyn29
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoDischarge Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_37 = happyReduce 4 29 happyReduction_37
happyReduction_37 (_ `HappyStk`
	(HappyAbsSyn30  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn29
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DischargeOver (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_38 = happySpecReduce_0  30 happyReduction_38
happyReduction_38  =  HappyAbsSyn30
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_39 = happySpecReduce_1  30 happyReduction_39
happyReduction_39 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn30
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_39 _  = notHappyAtAll 

happyReduce_40 = happySpecReduce_3  30 happyReduction_40
happyReduction_40 (HappyAbsSyn30  happy_var_3)
	_
	(HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn30
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_40 _ _ _  = notHappyAtAll 

happyReduce_41 = happyReduce 8 31 happyReduction_41
happyReduction_41 ((HappyAbsSyn34  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn35  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_42 = happyReduce 8 31 happyReduction_42
happyReduction_42 ((HappyAbsSyn34  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn35  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_43 = happyReduce 4 31 happyReduction_43
happyReduction_43 ((HappyAbsSyn34  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn35  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_44 = happyReduce 6 31 happyReduction_44
happyReduction_44 ((HappyAbsSyn34  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn35  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_45 = happySpecReduce_3  31 happyReduction_45
happyReduction_45 (HappyAbsSyn31  happy_var_3)
	_
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_45 _ _ _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_3  31 happyReduction_46
happyReduction_46 (HappyAbsSyn31  happy_var_3)
	_
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_46 _ _ _  = notHappyAtAll 

happyReduce_47 = happySpecReduce_1  31 happyReduction_47
happyReduction_47 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_47 _  = notHappyAtAll 

happyReduce_48 = happySpecReduce_2  32 happyReduction_48
happyReduction_48 (HappyAbsSyn31  happy_var_2)
	(HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_48 _ _  = notHappyAtAll 

happyReduce_49 = happySpecReduce_1  32 happyReduction_49
happyReduction_49 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_49 _  = notHappyAtAll 

happyReduce_50 = happySpecReduce_2  33 happyReduction_50
happyReduction_50 (HappyAbsSyn31  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_50 _ _  = notHappyAtAll 

happyReduce_51 = happySpecReduce_2  33 happyReduction_51
happyReduction_51 (HappyAbsSyn31  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_51 _ _  = notHappyAtAll 

happyReduce_52 = happySpecReduce_1  33 happyReduction_52
happyReduction_52 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_52 _  = notHappyAtAll 

happyReduce_53 = happySpecReduce_1  33 happyReduction_53
happyReduction_53 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_53 _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_1  33 happyReduction_54
happyReduction_54 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_54 _  = notHappyAtAll 

happyReduce_55 = happySpecReduce_1  33 happyReduction_55
happyReduction_55 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn31
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happyReduce 8 33 happyReduction_56
happyReduction_56 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_57 = happyReduce 4 33 happyReduction_57
happyReduction_57 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_58 = happyReduce 8 33 happyReduction_58
happyReduction_58 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_59 = happyReduce 5 33 happyReduction_59
happyReduction_59 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_60 = happyReduce 5 33 happyReduction_60
happyReduction_60 (_ `HappyStk`
	(HappyAbsSyn31  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn31  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_61 = happySpecReduce_3  33 happyReduction_61
happyReduction_61 _
	(HappyAbsSyn31  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_61 _ _ _  = notHappyAtAll 

happyReduce_62 = happySpecReduce_1  34 happyReduction_62
happyReduction_62 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn34
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_62 _  = notHappyAtAll 

happyReduce_63 = happySpecReduce_1  35 happyReduction_63
happyReduction_63 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_63 _  = notHappyAtAll 

happyReduce_64 = happySpecReduce_1  35 happyReduction_64
happyReduction_64 (HappyAbsSyn19  happy_var_1)
	 =  HappyAbsSyn35
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_64 _  = notHappyAtAll 

happyReduce_65 = happyReduce 5 35 happyReduction_65
happyReduction_65 (_ `HappyStk`
	(HappyAbsSyn35  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn35  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn35
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 73 73 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 36;
	PT _ (TS _ 2) -> cont 37;
	PT _ (TS _ 3) -> cont 38;
	PT _ (TS _ 4) -> cont 39;
	PT _ (TS _ 5) -> cont 40;
	PT _ (TS _ 6) -> cont 41;
	PT _ (TS _ 7) -> cont 42;
	PT _ (TS _ 8) -> cont 43;
	PT _ (TS _ 9) -> cont 44;
	PT _ (TS _ 10) -> cont 45;
	PT _ (TS _ 11) -> cont 46;
	PT _ (TS _ 12) -> cont 47;
	PT _ (TS _ 13) -> cont 48;
	PT _ (TS _ 14) -> cont 49;
	PT _ (TS _ 15) -> cont 50;
	PT _ (TS _ 16) -> cont 51;
	PT _ (TS _ 17) -> cont 52;
	PT _ (TS _ 18) -> cont 53;
	PT _ (TS _ 19) -> cont 54;
	PT _ (TS _ 20) -> cont 55;
	PT _ (TS _ 21) -> cont 56;
	PT _ (TS _ 22) -> cont 57;
	PT _ (TS _ 23) -> cont 58;
	PT _ (TS _ 24) -> cont 59;
	PT _ (TS _ 25) -> cont 60;
	PT _ (TS _ 26) -> cont 61;
	PT _ (TS _ 27) -> cont 62;
	PT _ (TS _ 28) -> cont 63;
	PT _ (TS _ 29) -> cont 64;
	PT _ (TS _ 30) -> cont 65;
	PT _ (TS _ 31) -> cont 66;
	PT _ (TS _ 32) -> cont 67;
	PT _ (TS _ 33) -> cont 68;
	PT _ (TS _ 34) -> cont 69;
	PT _ (TS _ 35) -> cont 70;
	PT _ (TS _ 36) -> cont 71;
	PT _ (T_VarIdent _) -> cont 72;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 73 tk tks = happyError' (tks, explist)
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
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn20 z -> happyReturn z; _other -> notHappyAtAll })

pListModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn21 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn22 z -> happyReturn z; _other -> notHappyAtAll })

pParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn23 z -> happyReturn z; _other -> notHappyAtAll })

pListParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn24 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn25 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn26 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn27 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn28 z -> happyReturn z; _other -> notHappyAtAll })

pDischarge_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn29 z -> happyReturn z; _other -> notHappyAtAll })

pListVarIdent_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn30 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_12 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_13 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_14 tks) (\x -> case x of {HappyAbsSyn34 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_15 tks) (\x -> case x of {HappyAbsSyn35 z -> happyReturn z; _other -> notHappyAtAll })

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
