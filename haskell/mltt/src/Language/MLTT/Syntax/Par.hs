{-# OPTIONS_GHC -w #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns -fno-warn-overlapping-patterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Language.MLTT.Syntax.Par
  ( happyError
  , myLexer
  , pProgram
  , pListUnit
  , pUnit
  , pModule
  , pInclude
  , pListInclude
  , pRefinement
  , pFixed
  , pListFixed
  , pTelescopeDecl
  , pParam
  , pListParam
  , pImport
  , pListImport
  , pDecl
  , pListDecl
  , pDischarge
  , pListVarIdent
  , pTerm
  , pScopedTerm9
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
	| HappyAbsSyn27 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.VarIdent))
	| HappyAbsSyn28 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Program))
	| HappyAbsSyn29 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Unit]))
	| HappyAbsSyn30 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Unit))
	| HappyAbsSyn31 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Module))
	| HappyAbsSyn32 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Include))
	| HappyAbsSyn33 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Include]))
	| HappyAbsSyn34 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Refinement))
	| HappyAbsSyn35 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Fixed))
	| HappyAbsSyn36 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Fixed]))
	| HappyAbsSyn37 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.TelescopeDecl))
	| HappyAbsSyn38 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Param))
	| HappyAbsSyn39 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Param]))
	| HappyAbsSyn40 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Import))
	| HappyAbsSyn41 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Import]))
	| HappyAbsSyn42 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Decl))
	| HappyAbsSyn43 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.Decl]))
	| HappyAbsSyn44 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Discharge))
	| HappyAbsSyn45 ((Language.MLTT.Syntax.Abs.BNFC'Position, [Language.MLTT.Syntax.Abs.VarIdent]))
	| HappyAbsSyn46 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Term))
	| HappyAbsSyn47 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.ScopedTerm))
	| HappyAbsSyn51 ((Language.MLTT.Syntax.Abs.BNFC'Position, Language.MLTT.Syntax.Abs.Pattern))

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
 action_172,
 action_173,
 action_174,
 action_175,
 action_176,
 action_177,
 action_178,
 action_179,
 action_180,
 action_181,
 action_182,
 action_183,
 action_184,
 action_185,
 action_186,
 action_187,
 action_188,
 action_189,
 action_190,
 action_191,
 action_192,
 action_193,
 action_194,
 action_195,
 action_196,
 action_197,
 action_198,
 action_199,
 action_200,
 action_201,
 action_202,
 action_203,
 action_204,
 action_205,
 action_206,
 action_207,
 action_208,
 action_209,
 action_210,
 action_211,
 action_212,
 action_213,
 action_214,
 action_215,
 action_216,
 action_217,
 action_218,
 action_219,
 action_220,
 action_221,
 action_222,
 action_223,
 action_224,
 action_225,
 action_226,
 action_227,
 action_228,
 action_229,
 action_230,
 action_231,
 action_232,
 action_233,
 action_234,
 action_235,
 action_236,
 action_237 :: () => Prelude.Int -> ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

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
 happyReduce_66,
 happyReduce_67,
 happyReduce_68,
 happyReduce_69,
 happyReduce_70,
 happyReduce_71,
 happyReduce_72,
 happyReduce_73,
 happyReduce_74,
 happyReduce_75,
 happyReduce_76,
 happyReduce_77,
 happyReduce_78,
 happyReduce_79,
 happyReduce_80,
 happyReduce_81,
 happyReduce_82,
 happyReduce_83,
 happyReduce_84,
 happyReduce_85,
 happyReduce_86,
 happyReduce_87,
 happyReduce_88,
 happyReduce_89,
 happyReduce_90,
 happyReduce_91,
 happyReduce_92 :: () => ({-HappyReduction (Err) = -}
	   Prelude.Int 
	-> (Token)
	-> HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)
	-> [HappyState (Token) (HappyStk HappyAbsSyn -> [(Token)] -> (Err) HappyAbsSyn)] 
	-> HappyStk HappyAbsSyn 
	-> [(Token)] -> (Err) HappyAbsSyn)

happyExpList :: Happy_Data_Array.Array Prelude.Int Prelude.Int
happyExpList = Happy_Data_Array.listArray (0,511) ([0,0,0,0,2080,0,0,0,0,0,130,0,0,0,0,8192,8,0,0,0,0,512,0,0,0,0,0,8,0,0,0,0,32768,0,0,0,0,16384,0,0,0,0,0,0,0,16384,0,0,0,0,0,1024,0,0,0,0,128,0,0,0,2048,0,0,0,0,0,128,0,0,0,0,0,0,2,0,0,0,0,8192,0,0,0,0,0,49600,2,0,0,0,0,11292,0,0,0,0,0,256,0,0,0,0,0,0,64,0,0,2048,4120,15892,7,0,0,128,2,18432,0,0,0,6152,5120,1840,0,0,32768,384,320,115,0,0,2048,4120,15892,7,0,0,128,2,16384,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8200,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6152,5120,1905,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32896,16641,29665,0,0,0,8,0,0,0,0,32768,0,0,0,0,0,2048,32,0,4,0,0,128,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,2048,0,0,0,0,0,128,2,16384,0,0,0,6152,5120,1840,0,0,32768,384,320,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,384,320,115,0,0,0,0,0,0,0,0,128,2,18432,0,0,0,6152,5136,1854,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,6152,5136,1854,0,0,32768,384,57665,115,0,0,0,0,0,4,0,0,0,0,16384,0,0,0,0,0,1024,0,0,0,4096,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,16,0,0,0,0,8192,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,130,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,0,0,0,0,16384,0,0,0,0,0,0,0,0,0,0,0,0,0,1024,0,0,0,0,0,64,0,0,2048,4120,15892,7,0,0,0,128,0,0,0,0,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,32,0,0,0,0,4096,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,49600,2,0,0,0,0,0,16384,0,0,0,0,0,1024,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,32,32768,4,0,0,128,2,16384,0,0,0,8200,0,1024,0,0,32768,384,57665,115,0,0,0,4,0,0,0,0,32896,16641,29665,0,0,0,6152,5136,1854,0,0,0,11,0,0,0,0,2048,4120,15892,7,0,0,32896,16641,29665,0,0,0,32,0,0,0,0,32768,512,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,384,57665,115,0,0,2048,4120,15892,7,0,0,512,0,0,0,0,0,32,0,0,0,0,32768,384,57665,115,0,0,4096,0,0,0,0,0,2176,2,16384,0,0,0,128,0,0,0,0,32768,512,0,72,0,0,2048,4120,15892,7,0,0,0,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,0,2048,4120,15892,7,0,0,2048,0,0,0,0,0,0,16384,0,0,0,0,0,16,0,0,0,0,0,0,0,0,0,32896,16641,29665,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,32768,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,512,0,0,0,0,0,17,0,0,0,0,32768,0,0,0,0,0,0,11292,0,0,0,0,6152,5136,1854,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32768,384,57665,115,0,0,34816,32,0,4,0,0,32896,16641,29665,0,0,0,0,0,0,0,0,0,16384,0,0,0,0,2048,4120,15892,7,0,0,32896,16641,29665,0,0,0,16,0,0,0,0,0,1,0,0,0,0,4096,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8192,0,0,0,0,0,512,0,0,0,0,0,6152,5136,1854,0,0,0,1,0,0,0,0,34816,32,0,4,0,0,32896,16641,29665,0,0,0,16,0,0,0,0,0,16,0,0,0,0,0,0,128,0,0,0,32896,16641,29665,0,0,0,0,0,0,0,0,32768,384,57665,115,0,0,0,0,0,0,0,0,0,32,0,0,0,0,49152,705,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,6152,5136,1854,0,0,0,0,4096,0,0,0,4096,0,0,0,0,0,2048,0,0,0,0,0,6152,5136,1854,0,0,0,0,0,4,0,0,0,0,0,0,0,0,32896,16641,29665,0,0,0,6152,5136,1854,0,0,0,1,0,0,0,0,4096,0,0,0,0,0,32896,16641,29665,0,0,0,16,0,0,0,0,32768,384,57665,115,0,0,0,0,16384,0,0,0,32896,16641,29665,0,0,0,0,0,0,0,0,32768,384,57665,115,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2048,4120,15892,7,0,0,256,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6152,5136,1854,0,0,0,0,0,4,0,0,0,0,0,0,0,0,32896,16641,29665,0,0,0,0,0,0,0,0,0,0,0,0,0
	])

{-# NOINLINE happyExpListPerState #-}
happyExpListPerState st =
    token_strs_expected
  where token_strs = ["error","%dummy","%start_pProgram_internal","%start_pListUnit_internal","%start_pUnit_internal","%start_pModule_internal","%start_pInclude_internal","%start_pListInclude_internal","%start_pRefinement_internal","%start_pFixed_internal","%start_pListFixed_internal","%start_pTelescopeDecl_internal","%start_pParam_internal","%start_pListParam_internal","%start_pImport_internal","%start_pListImport_internal","%start_pDecl_internal","%start_pListDecl_internal","%start_pDischarge_internal","%start_pListVarIdent_internal","%start_pTerm_internal","%start_pScopedTerm9_internal","%start_pTerm1_internal","%start_pTerm2_internal","%start_pScopedTerm_internal","%start_pPattern_internal","VarIdent","Program","ListUnit","Unit","Module","Include","ListInclude","Refinement","Fixed","ListFixed","TelescopeDecl","Param","ListParam","Import","ListImport","Decl","ListDecl","Discharge","ListVarIdent","Term","ScopedTerm9","Term1","Term2","ScopedTerm","Pattern","'('","')'","','","'/'","':'","':='","';'","'='","'Id'","'J'","'_'","'check'","'compute'","'def'","'import'","'in'","'include'","'let'","'module'","'namespace'","'open'","'over'","'private'","'refl'","'telescope'","'tt'","'where'","'{'","'}'","'\215'","'\928'","'\931'","'\955'","'\960\8321'","'\960\8322'","'\8594'","'\8658'","'\120140'","'\120793'","L_VarIdent","%eof"]
        bit_start = st Prelude.* 92
        bit_end = (st Prelude.+ 1) Prelude.* 92
        read_bit = readArrayBit happyExpList
        bits = Prelude.map read_bit [bit_start..bit_end Prelude.- 1]
        bits_indexed = Prelude.zip bits [0..91]
        token_strs_expected = Prelude.concatMap f bits_indexed
        f (Prelude.False, _) = []
        f (Prelude.True, nr) = [token_strs Prelude.!! nr]

action_0 (70) = happyShift action_88
action_0 (76) = happyShift action_76
action_0 (28) = happyGoto action_94
action_0 (29) = happyGoto action_95
action_0 (30) = happyGoto action_93
action_0 (31) = happyGoto action_90
action_0 (37) = happyGoto action_91
action_0 _ = happyReduce_26

action_1 (70) = happyShift action_88
action_1 (76) = happyShift action_76
action_1 (29) = happyGoto action_92
action_1 (30) = happyGoto action_93
action_1 (31) = happyGoto action_90
action_1 (37) = happyGoto action_91
action_1 _ = happyReduce_26

action_2 (70) = happyShift action_88
action_2 (76) = happyShift action_76
action_2 (30) = happyGoto action_89
action_2 (31) = happyGoto action_90
action_2 (37) = happyGoto action_91
action_2 _ = happyFail (happyExpListPerState 2)

action_3 (70) = happyShift action_88
action_3 (31) = happyGoto action_87
action_3 _ = happyFail (happyExpListPerState 3)

action_4 (68) = happyShift action_85
action_4 (32) = happyGoto action_86
action_4 _ = happyFail (happyExpListPerState 4)

action_5 (68) = happyShift action_85
action_5 (32) = happyGoto action_83
action_5 (33) = happyGoto action_84
action_5 _ = happyReduce_32

action_6 (55) = happyShift action_82
action_6 (34) = happyGoto action_81
action_6 _ = happyReduce_34

action_7 (91) = happyShift action_25
action_7 (27) = happyGoto action_77
action_7 (35) = happyGoto action_80
action_7 _ = happyFail (happyExpListPerState 7)

action_8 (91) = happyShift action_25
action_8 (27) = happyGoto action_77
action_8 (35) = happyGoto action_78
action_8 (36) = happyGoto action_79
action_8 _ = happyReduce_37

action_9 (76) = happyShift action_76
action_9 (37) = happyGoto action_75
action_9 _ = happyFail (happyExpListPerState 9)

action_10 (52) = happyShift action_73
action_10 (38) = happyGoto action_74
action_10 _ = happyFail (happyExpListPerState 10)

action_11 (52) = happyShift action_73
action_11 (38) = happyGoto action_71
action_11 (39) = happyGoto action_72
action_11 _ = happyReduce_43

action_12 (66) = happyShift action_69
action_12 (40) = happyGoto action_70
action_12 _ = happyFail (happyExpListPerState 12)

action_13 (66) = happyShift action_69
action_13 (40) = happyGoto action_67
action_13 (41) = happyGoto action_68
action_13 _ = happyReduce_46

action_14 (63) = happyShift action_60
action_14 (64) = happyShift action_61
action_14 (65) = happyShift action_62
action_14 (71) = happyShift action_63
action_14 (72) = happyShift action_64
action_14 (74) = happyShift action_65
action_14 (42) = happyGoto action_66
action_14 _ = happyFail (happyExpListPerState 14)

action_15 (63) = happyShift action_60
action_15 (64) = happyShift action_61
action_15 (65) = happyShift action_62
action_15 (71) = happyShift action_63
action_15 (72) = happyShift action_64
action_15 (74) = happyShift action_65
action_15 (42) = happyGoto action_58
action_15 (43) = happyGoto action_59
action_15 _ = happyReduce_54

action_16 (73) = happyShift action_57
action_16 (44) = happyGoto action_56
action_16 _ = happyReduce_57

action_17 (91) = happyShift action_25
action_17 (27) = happyGoto action_54
action_17 (45) = happyGoto action_55
action_17 _ = happyReduce_59

action_18 (52) = happyShift action_35
action_18 (60) = happyShift action_36
action_18 (61) = happyShift action_37
action_18 (69) = happyShift action_38
action_18 (75) = happyShift action_39
action_18 (77) = happyShift action_40
action_18 (82) = happyShift action_41
action_18 (83) = happyShift action_42
action_18 (84) = happyShift action_43
action_18 (85) = happyShift action_44
action_18 (86) = happyShift action_45
action_18 (89) = happyShift action_46
action_18 (90) = happyShift action_47
action_18 (91) = happyShift action_25
action_18 (27) = happyGoto action_30
action_18 (46) = happyGoto action_53
action_18 (48) = happyGoto action_32
action_18 (49) = happyGoto action_33
action_18 _ = happyFail (happyExpListPerState 18)

action_19 (52) = happyShift action_28
action_19 (62) = happyShift action_29
action_19 (88) = happyShift action_52
action_19 (91) = happyShift action_25
action_19 (27) = happyGoto action_26
action_19 (47) = happyGoto action_50
action_19 (51) = happyGoto action_51
action_19 _ = happyFail (happyExpListPerState 19)

action_20 (52) = happyShift action_35
action_20 (60) = happyShift action_36
action_20 (61) = happyShift action_37
action_20 (75) = happyShift action_39
action_20 (77) = happyShift action_40
action_20 (85) = happyShift action_44
action_20 (86) = happyShift action_45
action_20 (89) = happyShift action_46
action_20 (90) = happyShift action_47
action_20 (91) = happyShift action_25
action_20 (27) = happyGoto action_30
action_20 (48) = happyGoto action_49
action_20 (49) = happyGoto action_33
action_20 _ = happyFail (happyExpListPerState 20)

action_21 (52) = happyShift action_35
action_21 (60) = happyShift action_36
action_21 (61) = happyShift action_37
action_21 (75) = happyShift action_39
action_21 (77) = happyShift action_40
action_21 (85) = happyShift action_44
action_21 (86) = happyShift action_45
action_21 (89) = happyShift action_46
action_21 (90) = happyShift action_47
action_21 (91) = happyShift action_25
action_21 (27) = happyGoto action_30
action_21 (49) = happyGoto action_48
action_21 _ = happyFail (happyExpListPerState 21)

action_22 (52) = happyShift action_35
action_22 (60) = happyShift action_36
action_22 (61) = happyShift action_37
action_22 (69) = happyShift action_38
action_22 (75) = happyShift action_39
action_22 (77) = happyShift action_40
action_22 (82) = happyShift action_41
action_22 (83) = happyShift action_42
action_22 (84) = happyShift action_43
action_22 (85) = happyShift action_44
action_22 (86) = happyShift action_45
action_22 (89) = happyShift action_46
action_22 (90) = happyShift action_47
action_22 (91) = happyShift action_25
action_22 (27) = happyGoto action_30
action_22 (46) = happyGoto action_31
action_22 (48) = happyGoto action_32
action_22 (49) = happyGoto action_33
action_22 (50) = happyGoto action_34
action_22 _ = happyFail (happyExpListPerState 22)

action_23 (52) = happyShift action_28
action_23 (62) = happyShift action_29
action_23 (91) = happyShift action_25
action_23 (27) = happyGoto action_26
action_23 (51) = happyGoto action_27
action_23 _ = happyFail (happyExpListPerState 23)

action_24 (91) = happyShift action_25
action_24 _ = happyFail (happyExpListPerState 24)

action_25 _ = happyReduce_24

action_26 _ = happyReduce_91

action_27 (92) = happyAccept
action_27 _ = happyFail (happyExpListPerState 27)

action_28 (52) = happyShift action_28
action_28 (62) = happyShift action_29
action_28 (91) = happyShift action_25
action_28 (27) = happyGoto action_26
action_28 (51) = happyGoto action_132
action_28 _ = happyFail (happyExpListPerState 28)

action_29 _ = happyReduce_90

action_30 _ = happyReduce_82

action_31 _ = happyReduce_89

action_32 (52) = happyShift action_35
action_32 (60) = happyShift action_36
action_32 (61) = happyShift action_37
action_32 (75) = happyShift action_39
action_32 (77) = happyShift action_40
action_32 (81) = happyShift action_130
action_32 (85) = happyShift action_44
action_32 (86) = happyShift action_45
action_32 (87) = happyShift action_131
action_32 (89) = happyShift action_46
action_32 (90) = happyShift action_47
action_32 (91) = happyShift action_25
action_32 (27) = happyGoto action_30
action_32 (49) = happyGoto action_119
action_32 _ = happyReduce_72

action_33 _ = happyReduce_76

action_34 (92) = happyAccept
action_34 _ = happyFail (happyExpListPerState 34)

action_35 (52) = happyShift action_35
action_35 (60) = happyShift action_36
action_35 (61) = happyShift action_37
action_35 (69) = happyShift action_38
action_35 (75) = happyShift action_39
action_35 (77) = happyShift action_40
action_35 (82) = happyShift action_41
action_35 (83) = happyShift action_42
action_35 (84) = happyShift action_43
action_35 (85) = happyShift action_44
action_35 (86) = happyShift action_45
action_35 (89) = happyShift action_46
action_35 (90) = happyShift action_47
action_35 (91) = happyShift action_25
action_35 (27) = happyGoto action_30
action_35 (46) = happyGoto action_129
action_35 (48) = happyGoto action_32
action_35 (49) = happyGoto action_33
action_35 _ = happyFail (happyExpListPerState 35)

action_36 (52) = happyShift action_128
action_36 _ = happyFail (happyExpListPerState 36)

action_37 (52) = happyShift action_127
action_37 _ = happyFail (happyExpListPerState 37)

action_38 (52) = happyShift action_28
action_38 (62) = happyShift action_29
action_38 (91) = happyShift action_25
action_38 (27) = happyGoto action_26
action_38 (51) = happyGoto action_126
action_38 _ = happyFail (happyExpListPerState 38)

action_39 (52) = happyShift action_125
action_39 _ = happyFail (happyExpListPerState 39)

action_40 _ = happyReduce_81

action_41 (52) = happyShift action_124
action_41 _ = happyFail (happyExpListPerState 41)

action_42 (52) = happyShift action_123
action_42 _ = happyFail (happyExpListPerState 42)

action_43 (52) = happyShift action_28
action_43 (62) = happyShift action_29
action_43 (91) = happyShift action_25
action_43 (27) = happyGoto action_26
action_43 (51) = happyGoto action_122
action_43 _ = happyFail (happyExpListPerState 43)

action_44 (52) = happyShift action_35
action_44 (60) = happyShift action_36
action_44 (61) = happyShift action_37
action_44 (75) = happyShift action_39
action_44 (77) = happyShift action_40
action_44 (85) = happyShift action_44
action_44 (86) = happyShift action_45
action_44 (89) = happyShift action_46
action_44 (90) = happyShift action_47
action_44 (91) = happyShift action_25
action_44 (27) = happyGoto action_30
action_44 (49) = happyGoto action_121
action_44 _ = happyFail (happyExpListPerState 44)

action_45 (52) = happyShift action_35
action_45 (60) = happyShift action_36
action_45 (61) = happyShift action_37
action_45 (75) = happyShift action_39
action_45 (77) = happyShift action_40
action_45 (85) = happyShift action_44
action_45 (86) = happyShift action_45
action_45 (89) = happyShift action_46
action_45 (90) = happyShift action_47
action_45 (91) = happyShift action_25
action_45 (27) = happyGoto action_30
action_45 (49) = happyGoto action_120
action_45 _ = happyFail (happyExpListPerState 45)

action_46 _ = happyReduce_79

action_47 _ = happyReduce_80

action_48 (92) = happyAccept
action_48 _ = happyFail (happyExpListPerState 48)

action_49 (52) = happyShift action_35
action_49 (60) = happyShift action_36
action_49 (61) = happyShift action_37
action_49 (75) = happyShift action_39
action_49 (77) = happyShift action_40
action_49 (85) = happyShift action_44
action_49 (86) = happyShift action_45
action_49 (89) = happyShift action_46
action_49 (90) = happyShift action_47
action_49 (91) = happyShift action_25
action_49 (92) = happyAccept
action_49 (27) = happyGoto action_30
action_49 (49) = happyGoto action_119
action_49 _ = happyFail (happyExpListPerState 49)

action_50 (92) = happyAccept
action_50 _ = happyFail (happyExpListPerState 50)

action_51 (52) = happyShift action_28
action_51 (62) = happyShift action_29
action_51 (88) = happyShift action_52
action_51 (91) = happyShift action_25
action_51 (27) = happyGoto action_26
action_51 (47) = happyGoto action_118
action_51 (51) = happyGoto action_51
action_51 _ = happyFail (happyExpListPerState 51)

action_52 (52) = happyShift action_35
action_52 (60) = happyShift action_36
action_52 (61) = happyShift action_37
action_52 (69) = happyShift action_38
action_52 (75) = happyShift action_39
action_52 (77) = happyShift action_40
action_52 (82) = happyShift action_41
action_52 (83) = happyShift action_42
action_52 (84) = happyShift action_43
action_52 (85) = happyShift action_44
action_52 (86) = happyShift action_45
action_52 (89) = happyShift action_46
action_52 (90) = happyShift action_47
action_52 (91) = happyShift action_25
action_52 (27) = happyGoto action_30
action_52 (46) = happyGoto action_117
action_52 (48) = happyGoto action_32
action_52 (49) = happyGoto action_33
action_52 _ = happyFail (happyExpListPerState 52)

action_53 (92) = happyAccept
action_53 _ = happyFail (happyExpListPerState 53)

action_54 (54) = happyShift action_116
action_54 _ = happyReduce_60

action_55 (92) = happyAccept
action_55 _ = happyFail (happyExpListPerState 55)

action_56 (92) = happyAccept
action_56 _ = happyFail (happyExpListPerState 56)

action_57 (52) = happyShift action_115
action_57 _ = happyFail (happyExpListPerState 57)

action_58 (58) = happyShift action_114
action_58 _ = happyReduce_55

action_59 (92) = happyAccept
action_59 _ = happyFail (happyExpListPerState 59)

action_60 (52) = happyShift action_35
action_60 (60) = happyShift action_36
action_60 (61) = happyShift action_37
action_60 (69) = happyShift action_38
action_60 (75) = happyShift action_39
action_60 (77) = happyShift action_40
action_60 (82) = happyShift action_41
action_60 (83) = happyShift action_42
action_60 (84) = happyShift action_43
action_60 (85) = happyShift action_44
action_60 (86) = happyShift action_45
action_60 (89) = happyShift action_46
action_60 (90) = happyShift action_47
action_60 (91) = happyShift action_25
action_60 (27) = happyGoto action_30
action_60 (46) = happyGoto action_113
action_60 (48) = happyGoto action_32
action_60 (49) = happyGoto action_33
action_60 _ = happyFail (happyExpListPerState 60)

action_61 (52) = happyShift action_35
action_61 (60) = happyShift action_36
action_61 (61) = happyShift action_37
action_61 (69) = happyShift action_38
action_61 (75) = happyShift action_39
action_61 (77) = happyShift action_40
action_61 (82) = happyShift action_41
action_61 (83) = happyShift action_42
action_61 (84) = happyShift action_43
action_61 (85) = happyShift action_44
action_61 (86) = happyShift action_45
action_61 (89) = happyShift action_46
action_61 (90) = happyShift action_47
action_61 (91) = happyShift action_25
action_61 (27) = happyGoto action_30
action_61 (46) = happyGoto action_112
action_61 (48) = happyGoto action_32
action_61 (49) = happyGoto action_33
action_61 _ = happyFail (happyExpListPerState 61)

action_62 (91) = happyShift action_25
action_62 (27) = happyGoto action_111
action_62 _ = happyFail (happyExpListPerState 62)

action_63 (91) = happyShift action_25
action_63 (27) = happyGoto action_110
action_63 _ = happyFail (happyExpListPerState 63)

action_64 (91) = happyShift action_25
action_64 (27) = happyGoto action_109
action_64 _ = happyFail (happyExpListPerState 64)

action_65 (65) = happyShift action_108
action_65 _ = happyFail (happyExpListPerState 65)

action_66 (92) = happyAccept
action_66 _ = happyFail (happyExpListPerState 66)

action_67 (58) = happyShift action_107
action_67 _ = happyFail (happyExpListPerState 67)

action_68 (92) = happyAccept
action_68 _ = happyFail (happyExpListPerState 68)

action_69 (91) = happyShift action_25
action_69 (27) = happyGoto action_106
action_69 _ = happyFail (happyExpListPerState 69)

action_70 (92) = happyAccept
action_70 _ = happyFail (happyExpListPerState 70)

action_71 (52) = happyShift action_73
action_71 (38) = happyGoto action_71
action_71 (39) = happyGoto action_105
action_71 _ = happyReduce_43

action_72 (92) = happyAccept
action_72 _ = happyFail (happyExpListPerState 72)

action_73 (91) = happyShift action_25
action_73 (27) = happyGoto action_104
action_73 _ = happyFail (happyExpListPerState 73)

action_74 (92) = happyAccept
action_74 _ = happyFail (happyExpListPerState 74)

action_75 (92) = happyAccept
action_75 _ = happyFail (happyExpListPerState 75)

action_76 (91) = happyShift action_25
action_76 (27) = happyGoto action_103
action_76 _ = happyFail (happyExpListPerState 76)

action_77 (57) = happyShift action_102
action_77 _ = happyFail (happyExpListPerState 77)

action_78 (54) = happyShift action_101
action_78 _ = happyReduce_38

action_79 (92) = happyAccept
action_79 _ = happyFail (happyExpListPerState 79)

action_80 (92) = happyAccept
action_80 _ = happyFail (happyExpListPerState 80)

action_81 (92) = happyAccept
action_81 _ = happyFail (happyExpListPerState 81)

action_82 (79) = happyShift action_100
action_82 _ = happyFail (happyExpListPerState 82)

action_83 (68) = happyShift action_85
action_83 (32) = happyGoto action_83
action_83 (33) = happyGoto action_99
action_83 _ = happyReduce_32

action_84 (92) = happyAccept
action_84 _ = happyFail (happyExpListPerState 84)

action_85 (91) = happyShift action_25
action_85 (27) = happyGoto action_98
action_85 _ = happyFail (happyExpListPerState 85)

action_86 (92) = happyAccept
action_86 _ = happyFail (happyExpListPerState 86)

action_87 (92) = happyAccept
action_87 _ = happyFail (happyExpListPerState 87)

action_88 (91) = happyShift action_25
action_88 (27) = happyGoto action_97
action_88 _ = happyFail (happyExpListPerState 88)

action_89 (92) = happyAccept
action_89 _ = happyFail (happyExpListPerState 89)

action_90 _ = happyReduce_28

action_91 _ = happyReduce_29

action_92 (92) = happyAccept
action_92 _ = happyFail (happyExpListPerState 92)

action_93 (70) = happyShift action_88
action_93 (76) = happyShift action_76
action_93 (29) = happyGoto action_96
action_93 (30) = happyGoto action_93
action_93 (31) = happyGoto action_90
action_93 (37) = happyGoto action_91
action_93 _ = happyReduce_26

action_94 (92) = happyAccept
action_94 _ = happyFail (happyExpListPerState 94)

action_95 _ = happyReduce_25

action_96 _ = happyReduce_27

action_97 (68) = happyShift action_85
action_97 (32) = happyGoto action_83
action_97 (33) = happyGoto action_161
action_97 _ = happyReduce_32

action_98 (55) = happyShift action_82
action_98 (34) = happyGoto action_160
action_98 _ = happyReduce_34

action_99 _ = happyReduce_33

action_100 (91) = happyShift action_25
action_100 (27) = happyGoto action_77
action_100 (35) = happyGoto action_78
action_100 (36) = happyGoto action_159
action_100 _ = happyReduce_37

action_101 (91) = happyShift action_25
action_101 (27) = happyGoto action_77
action_101 (35) = happyGoto action_78
action_101 (36) = happyGoto action_158
action_101 _ = happyReduce_37

action_102 (52) = happyShift action_35
action_102 (60) = happyShift action_36
action_102 (61) = happyShift action_37
action_102 (69) = happyShift action_38
action_102 (75) = happyShift action_39
action_102 (77) = happyShift action_40
action_102 (82) = happyShift action_41
action_102 (83) = happyShift action_42
action_102 (84) = happyShift action_43
action_102 (85) = happyShift action_44
action_102 (86) = happyShift action_45
action_102 (89) = happyShift action_46
action_102 (90) = happyShift action_47
action_102 (91) = happyShift action_25
action_102 (27) = happyGoto action_30
action_102 (46) = happyGoto action_157
action_102 (48) = happyGoto action_32
action_102 (49) = happyGoto action_33
action_102 _ = happyFail (happyExpListPerState 102)

action_103 (68) = happyShift action_85
action_103 (32) = happyGoto action_83
action_103 (33) = happyGoto action_156
action_103 _ = happyReduce_32

action_104 (56) = happyShift action_155
action_104 _ = happyFail (happyExpListPerState 104)

action_105 _ = happyReduce_44

action_106 _ = happyReduce_45

action_107 (66) = happyShift action_69
action_107 (40) = happyGoto action_67
action_107 (41) = happyGoto action_154
action_107 _ = happyReduce_46

action_108 (91) = happyShift action_25
action_108 (27) = happyGoto action_153
action_108 _ = happyFail (happyExpListPerState 108)

action_109 _ = happyReduce_51

action_110 (78) = happyShift action_152
action_110 _ = happyFail (happyExpListPerState 110)

action_111 (73) = happyShift action_57
action_111 (44) = happyGoto action_151
action_111 _ = happyReduce_57

action_112 _ = happyReduce_53

action_113 (56) = happyShift action_150
action_113 _ = happyFail (happyExpListPerState 113)

action_114 (63) = happyShift action_60
action_114 (64) = happyShift action_61
action_114 (65) = happyShift action_62
action_114 (71) = happyShift action_63
action_114 (72) = happyShift action_64
action_114 (74) = happyShift action_65
action_114 (42) = happyGoto action_58
action_114 (43) = happyGoto action_149
action_114 _ = happyReduce_54

action_115 (91) = happyShift action_25
action_115 (27) = happyGoto action_54
action_115 (45) = happyGoto action_148
action_115 _ = happyReduce_59

action_116 (91) = happyShift action_25
action_116 (27) = happyGoto action_54
action_116 (45) = happyGoto action_147
action_116 _ = happyReduce_59

action_117 _ = happyReduce_73

action_118 _ = happyReduce_74

action_119 _ = happyReduce_75

action_120 _ = happyReduce_78

action_121 _ = happyReduce_77

action_122 (52) = happyShift action_28
action_122 (62) = happyShift action_29
action_122 (88) = happyShift action_146
action_122 (91) = happyShift action_25
action_122 (27) = happyGoto action_26
action_122 (51) = happyGoto action_145
action_122 _ = happyFail (happyExpListPerState 122)

action_123 (52) = happyShift action_28
action_123 (62) = happyShift action_29
action_123 (91) = happyShift action_25
action_123 (27) = happyGoto action_26
action_123 (51) = happyGoto action_144
action_123 _ = happyFail (happyExpListPerState 123)

action_124 (52) = happyShift action_28
action_124 (62) = happyShift action_29
action_124 (91) = happyShift action_25
action_124 (27) = happyGoto action_26
action_124 (51) = happyGoto action_143
action_124 _ = happyFail (happyExpListPerState 124)

action_125 (52) = happyShift action_35
action_125 (60) = happyShift action_36
action_125 (61) = happyShift action_37
action_125 (69) = happyShift action_38
action_125 (75) = happyShift action_39
action_125 (77) = happyShift action_40
action_125 (82) = happyShift action_41
action_125 (83) = happyShift action_42
action_125 (84) = happyShift action_43
action_125 (85) = happyShift action_44
action_125 (86) = happyShift action_45
action_125 (89) = happyShift action_46
action_125 (90) = happyShift action_47
action_125 (91) = happyShift action_25
action_125 (27) = happyGoto action_30
action_125 (46) = happyGoto action_142
action_125 (48) = happyGoto action_32
action_125 (49) = happyGoto action_33
action_125 _ = happyFail (happyExpListPerState 125)

action_126 (59) = happyShift action_141
action_126 _ = happyFail (happyExpListPerState 126)

action_127 (52) = happyShift action_35
action_127 (60) = happyShift action_36
action_127 (61) = happyShift action_37
action_127 (69) = happyShift action_38
action_127 (75) = happyShift action_39
action_127 (77) = happyShift action_40
action_127 (82) = happyShift action_41
action_127 (83) = happyShift action_42
action_127 (84) = happyShift action_43
action_127 (85) = happyShift action_44
action_127 (86) = happyShift action_45
action_127 (89) = happyShift action_46
action_127 (90) = happyShift action_47
action_127 (91) = happyShift action_25
action_127 (27) = happyGoto action_30
action_127 (46) = happyGoto action_140
action_127 (48) = happyGoto action_32
action_127 (49) = happyGoto action_33
action_127 _ = happyFail (happyExpListPerState 127)

action_128 (52) = happyShift action_35
action_128 (60) = happyShift action_36
action_128 (61) = happyShift action_37
action_128 (69) = happyShift action_38
action_128 (75) = happyShift action_39
action_128 (77) = happyShift action_40
action_128 (82) = happyShift action_41
action_128 (83) = happyShift action_42
action_128 (84) = happyShift action_43
action_128 (85) = happyShift action_44
action_128 (86) = happyShift action_45
action_128 (89) = happyShift action_46
action_128 (90) = happyShift action_47
action_128 (91) = happyShift action_25
action_128 (27) = happyGoto action_30
action_128 (46) = happyGoto action_139
action_128 (48) = happyGoto action_32
action_128 (49) = happyGoto action_33
action_128 _ = happyFail (happyExpListPerState 128)

action_129 (53) = happyShift action_136
action_129 (54) = happyShift action_137
action_129 (56) = happyShift action_138
action_129 _ = happyFail (happyExpListPerState 129)

action_130 (52) = happyShift action_35
action_130 (60) = happyShift action_36
action_130 (61) = happyShift action_37
action_130 (69) = happyShift action_38
action_130 (75) = happyShift action_39
action_130 (77) = happyShift action_40
action_130 (82) = happyShift action_41
action_130 (83) = happyShift action_42
action_130 (84) = happyShift action_43
action_130 (85) = happyShift action_44
action_130 (86) = happyShift action_45
action_130 (89) = happyShift action_46
action_130 (90) = happyShift action_47
action_130 (91) = happyShift action_25
action_130 (27) = happyGoto action_30
action_130 (46) = happyGoto action_135
action_130 (48) = happyGoto action_32
action_130 (49) = happyGoto action_33
action_130 _ = happyFail (happyExpListPerState 130)

action_131 (52) = happyShift action_35
action_131 (60) = happyShift action_36
action_131 (61) = happyShift action_37
action_131 (69) = happyShift action_38
action_131 (75) = happyShift action_39
action_131 (77) = happyShift action_40
action_131 (82) = happyShift action_41
action_131 (83) = happyShift action_42
action_131 (84) = happyShift action_43
action_131 (85) = happyShift action_44
action_131 (86) = happyShift action_45
action_131 (89) = happyShift action_46
action_131 (90) = happyShift action_47
action_131 (91) = happyShift action_25
action_131 (27) = happyGoto action_30
action_131 (46) = happyGoto action_134
action_131 (48) = happyGoto action_32
action_131 (49) = happyGoto action_33
action_131 _ = happyFail (happyExpListPerState 131)

action_132 (54) = happyShift action_133
action_132 _ = happyFail (happyExpListPerState 132)

action_133 (52) = happyShift action_28
action_133 (62) = happyShift action_29
action_133 (91) = happyShift action_25
action_133 (27) = happyGoto action_26
action_133 (51) = happyGoto action_182
action_133 _ = happyFail (happyExpListPerState 133)

action_134 _ = happyReduce_70

action_135 _ = happyReduce_71

action_136 _ = happyReduce_88

action_137 (52) = happyShift action_35
action_137 (60) = happyShift action_36
action_137 (61) = happyShift action_37
action_137 (69) = happyShift action_38
action_137 (75) = happyShift action_39
action_137 (77) = happyShift action_40
action_137 (82) = happyShift action_41
action_137 (83) = happyShift action_42
action_137 (84) = happyShift action_43
action_137 (85) = happyShift action_44
action_137 (86) = happyShift action_45
action_137 (89) = happyShift action_46
action_137 (90) = happyShift action_47
action_137 (91) = happyShift action_25
action_137 (27) = happyGoto action_30
action_137 (46) = happyGoto action_181
action_137 (48) = happyGoto action_32
action_137 (49) = happyGoto action_33
action_137 _ = happyFail (happyExpListPerState 137)

action_138 (52) = happyShift action_35
action_138 (60) = happyShift action_36
action_138 (61) = happyShift action_37
action_138 (69) = happyShift action_38
action_138 (75) = happyShift action_39
action_138 (77) = happyShift action_40
action_138 (82) = happyShift action_41
action_138 (83) = happyShift action_42
action_138 (84) = happyShift action_43
action_138 (85) = happyShift action_44
action_138 (86) = happyShift action_45
action_138 (89) = happyShift action_46
action_138 (90) = happyShift action_47
action_138 (91) = happyShift action_25
action_138 (27) = happyGoto action_30
action_138 (46) = happyGoto action_180
action_138 (48) = happyGoto action_32
action_138 (49) = happyGoto action_33
action_138 _ = happyFail (happyExpListPerState 138)

action_139 (54) = happyShift action_179
action_139 _ = happyFail (happyExpListPerState 139)

action_140 (54) = happyShift action_178
action_140 _ = happyFail (happyExpListPerState 140)

action_141 (52) = happyShift action_35
action_141 (60) = happyShift action_36
action_141 (61) = happyShift action_37
action_141 (69) = happyShift action_38
action_141 (75) = happyShift action_39
action_141 (77) = happyShift action_40
action_141 (82) = happyShift action_41
action_141 (83) = happyShift action_42
action_141 (84) = happyShift action_43
action_141 (85) = happyShift action_44
action_141 (86) = happyShift action_45
action_141 (89) = happyShift action_46
action_141 (90) = happyShift action_47
action_141 (91) = happyShift action_25
action_141 (27) = happyGoto action_30
action_141 (46) = happyGoto action_177
action_141 (48) = happyGoto action_32
action_141 (49) = happyGoto action_33
action_141 _ = happyFail (happyExpListPerState 141)

action_142 (53) = happyShift action_176
action_142 _ = happyFail (happyExpListPerState 142)

action_143 (52) = happyShift action_28
action_143 (56) = happyShift action_175
action_143 (62) = happyShift action_29
action_143 (91) = happyShift action_25
action_143 (27) = happyGoto action_26
action_143 (51) = happyGoto action_174
action_143 _ = happyFail (happyExpListPerState 143)

action_144 (56) = happyShift action_173
action_144 _ = happyFail (happyExpListPerState 144)

action_145 (52) = happyShift action_28
action_145 (62) = happyShift action_29
action_145 (88) = happyShift action_52
action_145 (91) = happyShift action_25
action_145 (27) = happyGoto action_26
action_145 (47) = happyGoto action_172
action_145 (51) = happyGoto action_51
action_145 _ = happyFail (happyExpListPerState 145)

action_146 (52) = happyShift action_35
action_146 (60) = happyShift action_36
action_146 (61) = happyShift action_37
action_146 (69) = happyShift action_38
action_146 (75) = happyShift action_39
action_146 (77) = happyShift action_40
action_146 (82) = happyShift action_41
action_146 (83) = happyShift action_42
action_146 (84) = happyShift action_43
action_146 (85) = happyShift action_44
action_146 (86) = happyShift action_45
action_146 (89) = happyShift action_46
action_146 (90) = happyShift action_47
action_146 (91) = happyShift action_25
action_146 (27) = happyGoto action_30
action_146 (46) = happyGoto action_31
action_146 (48) = happyGoto action_32
action_146 (49) = happyGoto action_33
action_146 (50) = happyGoto action_171
action_146 _ = happyFail (happyExpListPerState 146)

action_147 _ = happyReduce_61

action_148 (53) = happyShift action_170
action_148 _ = happyFail (happyExpListPerState 148)

action_149 _ = happyReduce_56

action_150 (52) = happyShift action_35
action_150 (60) = happyShift action_36
action_150 (61) = happyShift action_37
action_150 (69) = happyShift action_38
action_150 (75) = happyShift action_39
action_150 (77) = happyShift action_40
action_150 (82) = happyShift action_41
action_150 (83) = happyShift action_42
action_150 (84) = happyShift action_43
action_150 (85) = happyShift action_44
action_150 (86) = happyShift action_45
action_150 (89) = happyShift action_46
action_150 (90) = happyShift action_47
action_150 (91) = happyShift action_25
action_150 (27) = happyGoto action_30
action_150 (46) = happyGoto action_169
action_150 (48) = happyGoto action_32
action_150 (49) = happyGoto action_33
action_150 _ = happyFail (happyExpListPerState 150)

action_151 (56) = happyShift action_168
action_151 _ = happyFail (happyExpListPerState 151)

action_152 (79) = happyShift action_167
action_152 _ = happyFail (happyExpListPerState 152)

action_153 (73) = happyShift action_57
action_153 (44) = happyGoto action_166
action_153 _ = happyReduce_57

action_154 _ = happyReduce_47

action_155 (52) = happyShift action_35
action_155 (60) = happyShift action_36
action_155 (61) = happyShift action_37
action_155 (69) = happyShift action_38
action_155 (75) = happyShift action_39
action_155 (77) = happyShift action_40
action_155 (82) = happyShift action_41
action_155 (83) = happyShift action_42
action_155 (84) = happyShift action_43
action_155 (85) = happyShift action_44
action_155 (86) = happyShift action_45
action_155 (89) = happyShift action_46
action_155 (90) = happyShift action_47
action_155 (91) = happyShift action_25
action_155 (27) = happyGoto action_30
action_155 (46) = happyGoto action_165
action_155 (48) = happyGoto action_32
action_155 (49) = happyGoto action_33
action_155 _ = happyFail (happyExpListPerState 155)

action_156 (52) = happyShift action_73
action_156 (38) = happyGoto action_71
action_156 (39) = happyGoto action_164
action_156 _ = happyReduce_43

action_157 _ = happyReduce_36

action_158 _ = happyReduce_39

action_159 (80) = happyShift action_163
action_159 _ = happyFail (happyExpListPerState 159)

action_160 _ = happyReduce_31

action_161 (52) = happyShift action_73
action_161 (38) = happyGoto action_71
action_161 (39) = happyGoto action_162
action_161 _ = happyReduce_43

action_162 (58) = happyShift action_199
action_162 _ = happyFail (happyExpListPerState 162)

action_163 _ = happyReduce_35

action_164 (58) = happyShift action_198
action_164 _ = happyFail (happyExpListPerState 164)

action_165 (53) = happyShift action_196
action_165 (57) = happyShift action_197
action_165 _ = happyFail (happyExpListPerState 165)

action_166 (56) = happyShift action_195
action_166 _ = happyFail (happyExpListPerState 166)

action_167 (63) = happyShift action_60
action_167 (64) = happyShift action_61
action_167 (65) = happyShift action_62
action_167 (71) = happyShift action_63
action_167 (72) = happyShift action_64
action_167 (74) = happyShift action_65
action_167 (42) = happyGoto action_58
action_167 (43) = happyGoto action_194
action_167 _ = happyReduce_54

action_168 (52) = happyShift action_35
action_168 (60) = happyShift action_36
action_168 (61) = happyShift action_37
action_168 (69) = happyShift action_38
action_168 (75) = happyShift action_39
action_168 (77) = happyShift action_40
action_168 (82) = happyShift action_41
action_168 (83) = happyShift action_42
action_168 (84) = happyShift action_43
action_168 (85) = happyShift action_44
action_168 (86) = happyShift action_45
action_168 (89) = happyShift action_46
action_168 (90) = happyShift action_47
action_168 (91) = happyShift action_25
action_168 (27) = happyGoto action_30
action_168 (46) = happyGoto action_193
action_168 (48) = happyGoto action_32
action_168 (49) = happyGoto action_33
action_168 _ = happyFail (happyExpListPerState 168)

action_169 _ = happyReduce_52

action_170 _ = happyReduce_58

action_171 _ = happyReduce_64

action_172 _ = happyReduce_66

action_173 (52) = happyShift action_35
action_173 (60) = happyShift action_36
action_173 (61) = happyShift action_37
action_173 (69) = happyShift action_38
action_173 (75) = happyShift action_39
action_173 (77) = happyShift action_40
action_173 (82) = happyShift action_41
action_173 (83) = happyShift action_42
action_173 (84) = happyShift action_43
action_173 (85) = happyShift action_44
action_173 (86) = happyShift action_45
action_173 (89) = happyShift action_46
action_173 (90) = happyShift action_47
action_173 (91) = happyShift action_25
action_173 (27) = happyGoto action_30
action_173 (46) = happyGoto action_192
action_173 (48) = happyGoto action_32
action_173 (49) = happyGoto action_33
action_173 _ = happyFail (happyExpListPerState 173)

action_174 (52) = happyShift action_28
action_174 (56) = happyShift action_191
action_174 (62) = happyShift action_29
action_174 (91) = happyShift action_25
action_174 (27) = happyGoto action_26
action_174 (51) = happyGoto action_190
action_174 _ = happyFail (happyExpListPerState 174)

action_175 (52) = happyShift action_35
action_175 (60) = happyShift action_36
action_175 (61) = happyShift action_37
action_175 (69) = happyShift action_38
action_175 (75) = happyShift action_39
action_175 (77) = happyShift action_40
action_175 (82) = happyShift action_41
action_175 (83) = happyShift action_42
action_175 (84) = happyShift action_43
action_175 (85) = happyShift action_44
action_175 (86) = happyShift action_45
action_175 (89) = happyShift action_46
action_175 (90) = happyShift action_47
action_175 (91) = happyShift action_25
action_175 (27) = happyGoto action_30
action_175 (46) = happyGoto action_189
action_175 (48) = happyGoto action_32
action_175 (49) = happyGoto action_33
action_175 _ = happyFail (happyExpListPerState 175)

action_176 _ = happyReduce_84

action_177 (67) = happyShift action_188
action_177 _ = happyFail (happyExpListPerState 177)

action_178 (52) = happyShift action_35
action_178 (60) = happyShift action_36
action_178 (61) = happyShift action_37
action_178 (69) = happyShift action_38
action_178 (75) = happyShift action_39
action_178 (77) = happyShift action_40
action_178 (82) = happyShift action_41
action_178 (83) = happyShift action_42
action_178 (84) = happyShift action_43
action_178 (85) = happyShift action_44
action_178 (86) = happyShift action_45
action_178 (89) = happyShift action_46
action_178 (90) = happyShift action_47
action_178 (91) = happyShift action_25
action_178 (27) = happyGoto action_30
action_178 (46) = happyGoto action_187
action_178 (48) = happyGoto action_32
action_178 (49) = happyGoto action_33
action_178 _ = happyFail (happyExpListPerState 178)

action_179 (52) = happyShift action_35
action_179 (60) = happyShift action_36
action_179 (61) = happyShift action_37
action_179 (69) = happyShift action_38
action_179 (75) = happyShift action_39
action_179 (77) = happyShift action_40
action_179 (82) = happyShift action_41
action_179 (83) = happyShift action_42
action_179 (84) = happyShift action_43
action_179 (85) = happyShift action_44
action_179 (86) = happyShift action_45
action_179 (89) = happyShift action_46
action_179 (90) = happyShift action_47
action_179 (91) = happyShift action_25
action_179 (27) = happyGoto action_30
action_179 (46) = happyGoto action_186
action_179 (48) = happyGoto action_32
action_179 (49) = happyGoto action_33
action_179 _ = happyFail (happyExpListPerState 179)

action_180 (53) = happyShift action_185
action_180 _ = happyFail (happyExpListPerState 180)

action_181 (53) = happyShift action_184
action_181 _ = happyFail (happyExpListPerState 181)

action_182 (53) = happyShift action_183
action_182 _ = happyFail (happyExpListPerState 182)

action_183 _ = happyReduce_92

action_184 _ = happyReduce_86

action_185 _ = happyReduce_87

action_186 (54) = happyShift action_212
action_186 _ = happyFail (happyExpListPerState 186)

action_187 (54) = happyShift action_211
action_187 _ = happyFail (happyExpListPerState 187)

action_188 (52) = happyShift action_35
action_188 (60) = happyShift action_36
action_188 (61) = happyShift action_37
action_188 (69) = happyShift action_38
action_188 (75) = happyShift action_39
action_188 (77) = happyShift action_40
action_188 (82) = happyShift action_41
action_188 (83) = happyShift action_42
action_188 (84) = happyShift action_43
action_188 (85) = happyShift action_44
action_188 (86) = happyShift action_45
action_188 (89) = happyShift action_46
action_188 (90) = happyShift action_47
action_188 (91) = happyShift action_25
action_188 (27) = happyGoto action_30
action_188 (46) = happyGoto action_31
action_188 (48) = happyGoto action_32
action_188 (49) = happyGoto action_33
action_188 (50) = happyGoto action_210
action_188 _ = happyFail (happyExpListPerState 188)

action_189 (53) = happyShift action_209
action_189 _ = happyFail (happyExpListPerState 189)

action_190 (52) = happyShift action_28
action_190 (56) = happyShift action_208
action_190 (62) = happyShift action_29
action_190 (91) = happyShift action_25
action_190 (27) = happyGoto action_26
action_190 (51) = happyGoto action_207
action_190 _ = happyFail (happyExpListPerState 190)

action_191 (52) = happyShift action_35
action_191 (60) = happyShift action_36
action_191 (61) = happyShift action_37
action_191 (69) = happyShift action_38
action_191 (75) = happyShift action_39
action_191 (77) = happyShift action_40
action_191 (82) = happyShift action_41
action_191 (83) = happyShift action_42
action_191 (84) = happyShift action_43
action_191 (85) = happyShift action_44
action_191 (86) = happyShift action_45
action_191 (89) = happyShift action_46
action_191 (90) = happyShift action_47
action_191 (91) = happyShift action_25
action_191 (27) = happyGoto action_30
action_191 (46) = happyGoto action_206
action_191 (48) = happyGoto action_32
action_191 (49) = happyGoto action_33
action_191 _ = happyFail (happyExpListPerState 191)

action_192 (53) = happyShift action_205
action_192 _ = happyFail (happyExpListPerState 192)

action_193 (57) = happyShift action_204
action_193 _ = happyFail (happyExpListPerState 193)

action_194 (80) = happyShift action_203
action_194 _ = happyFail (happyExpListPerState 194)

action_195 (52) = happyShift action_35
action_195 (60) = happyShift action_36
action_195 (61) = happyShift action_37
action_195 (69) = happyShift action_38
action_195 (75) = happyShift action_39
action_195 (77) = happyShift action_40
action_195 (82) = happyShift action_41
action_195 (83) = happyShift action_42
action_195 (84) = happyShift action_43
action_195 (85) = happyShift action_44
action_195 (86) = happyShift action_45
action_195 (89) = happyShift action_46
action_195 (90) = happyShift action_47
action_195 (91) = happyShift action_25
action_195 (27) = happyGoto action_30
action_195 (46) = happyGoto action_202
action_195 (48) = happyGoto action_32
action_195 (49) = happyGoto action_33
action_195 _ = happyFail (happyExpListPerState 195)

action_196 _ = happyReduce_41

action_197 (52) = happyShift action_35
action_197 (60) = happyShift action_36
action_197 (61) = happyShift action_37
action_197 (69) = happyShift action_38
action_197 (75) = happyShift action_39
action_197 (77) = happyShift action_40
action_197 (82) = happyShift action_41
action_197 (83) = happyShift action_42
action_197 (84) = happyShift action_43
action_197 (85) = happyShift action_44
action_197 (86) = happyShift action_45
action_197 (89) = happyShift action_46
action_197 (90) = happyShift action_47
action_197 (91) = happyShift action_25
action_197 (27) = happyGoto action_30
action_197 (46) = happyGoto action_201
action_197 (48) = happyGoto action_32
action_197 (49) = happyGoto action_33
action_197 _ = happyFail (happyExpListPerState 197)

action_198 _ = happyReduce_40

action_199 (66) = happyShift action_69
action_199 (40) = happyGoto action_67
action_199 (41) = happyGoto action_200
action_199 _ = happyReduce_46

action_200 (63) = happyShift action_60
action_200 (64) = happyShift action_61
action_200 (65) = happyShift action_62
action_200 (71) = happyShift action_63
action_200 (72) = happyShift action_64
action_200 (74) = happyShift action_65
action_200 (42) = happyGoto action_58
action_200 (43) = happyGoto action_223
action_200 _ = happyReduce_54

action_201 (53) = happyShift action_222
action_201 _ = happyFail (happyExpListPerState 201)

action_202 (57) = happyShift action_221
action_202 _ = happyFail (happyExpListPerState 202)

action_203 _ = happyReduce_50

action_204 (52) = happyShift action_35
action_204 (60) = happyShift action_36
action_204 (61) = happyShift action_37
action_204 (69) = happyShift action_38
action_204 (75) = happyShift action_39
action_204 (77) = happyShift action_40
action_204 (82) = happyShift action_41
action_204 (83) = happyShift action_42
action_204 (84) = happyShift action_43
action_204 (85) = happyShift action_44
action_204 (86) = happyShift action_45
action_204 (89) = happyShift action_46
action_204 (90) = happyShift action_47
action_204 (91) = happyShift action_25
action_204 (27) = happyGoto action_30
action_204 (46) = happyGoto action_220
action_204 (48) = happyGoto action_32
action_204 (49) = happyGoto action_33
action_204 _ = happyFail (happyExpListPerState 204)

action_205 (81) = happyShift action_219
action_205 _ = happyFail (happyExpListPerState 205)

action_206 (53) = happyShift action_218
action_206 _ = happyFail (happyExpListPerState 206)

action_207 (56) = happyShift action_217
action_207 _ = happyFail (happyExpListPerState 207)

action_208 (52) = happyShift action_35
action_208 (60) = happyShift action_36
action_208 (61) = happyShift action_37
action_208 (69) = happyShift action_38
action_208 (75) = happyShift action_39
action_208 (77) = happyShift action_40
action_208 (82) = happyShift action_41
action_208 (83) = happyShift action_42
action_208 (84) = happyShift action_43
action_208 (85) = happyShift action_44
action_208 (86) = happyShift action_45
action_208 (89) = happyShift action_46
action_208 (90) = happyShift action_47
action_208 (91) = happyShift action_25
action_208 (27) = happyGoto action_30
action_208 (46) = happyGoto action_216
action_208 (48) = happyGoto action_32
action_208 (49) = happyGoto action_33
action_208 _ = happyFail (happyExpListPerState 208)

action_209 (87) = happyShift action_215
action_209 _ = happyFail (happyExpListPerState 209)

action_210 _ = happyReduce_65

action_211 (52) = happyShift action_35
action_211 (60) = happyShift action_36
action_211 (61) = happyShift action_37
action_211 (69) = happyShift action_38
action_211 (75) = happyShift action_39
action_211 (77) = happyShift action_40
action_211 (82) = happyShift action_41
action_211 (83) = happyShift action_42
action_211 (84) = happyShift action_43
action_211 (85) = happyShift action_44
action_211 (86) = happyShift action_45
action_211 (89) = happyShift action_46
action_211 (90) = happyShift action_47
action_211 (91) = happyShift action_25
action_211 (27) = happyGoto action_30
action_211 (46) = happyGoto action_214
action_211 (48) = happyGoto action_32
action_211 (49) = happyGoto action_33
action_211 _ = happyFail (happyExpListPerState 211)

action_212 (52) = happyShift action_35
action_212 (60) = happyShift action_36
action_212 (61) = happyShift action_37
action_212 (69) = happyShift action_38
action_212 (75) = happyShift action_39
action_212 (77) = happyShift action_40
action_212 (82) = happyShift action_41
action_212 (83) = happyShift action_42
action_212 (84) = happyShift action_43
action_212 (85) = happyShift action_44
action_212 (86) = happyShift action_45
action_212 (89) = happyShift action_46
action_212 (90) = happyShift action_47
action_212 (91) = happyShift action_25
action_212 (27) = happyGoto action_30
action_212 (46) = happyGoto action_213
action_212 (48) = happyGoto action_32
action_212 (49) = happyGoto action_33
action_212 _ = happyFail (happyExpListPerState 212)

action_213 (53) = happyShift action_231
action_213 _ = happyFail (happyExpListPerState 213)

action_214 (53) = happyShift action_230
action_214 _ = happyFail (happyExpListPerState 214)

action_215 (52) = happyShift action_35
action_215 (60) = happyShift action_36
action_215 (61) = happyShift action_37
action_215 (69) = happyShift action_38
action_215 (75) = happyShift action_39
action_215 (77) = happyShift action_40
action_215 (82) = happyShift action_41
action_215 (83) = happyShift action_42
action_215 (84) = happyShift action_43
action_215 (85) = happyShift action_44
action_215 (86) = happyShift action_45
action_215 (89) = happyShift action_46
action_215 (90) = happyShift action_47
action_215 (91) = happyShift action_25
action_215 (27) = happyGoto action_30
action_215 (46) = happyGoto action_31
action_215 (48) = happyGoto action_32
action_215 (49) = happyGoto action_33
action_215 (50) = happyGoto action_229
action_215 _ = happyFail (happyExpListPerState 215)

action_216 (53) = happyShift action_228
action_216 _ = happyFail (happyExpListPerState 216)

action_217 (52) = happyShift action_35
action_217 (60) = happyShift action_36
action_217 (61) = happyShift action_37
action_217 (69) = happyShift action_38
action_217 (75) = happyShift action_39
action_217 (77) = happyShift action_40
action_217 (82) = happyShift action_41
action_217 (83) = happyShift action_42
action_217 (84) = happyShift action_43
action_217 (85) = happyShift action_44
action_217 (86) = happyShift action_45
action_217 (89) = happyShift action_46
action_217 (90) = happyShift action_47
action_217 (91) = happyShift action_25
action_217 (27) = happyGoto action_30
action_217 (46) = happyGoto action_227
action_217 (48) = happyGoto action_32
action_217 (49) = happyGoto action_33
action_217 _ = happyFail (happyExpListPerState 217)

action_218 (87) = happyShift action_226
action_218 _ = happyFail (happyExpListPerState 218)

action_219 (52) = happyShift action_35
action_219 (60) = happyShift action_36
action_219 (61) = happyShift action_37
action_219 (69) = happyShift action_38
action_219 (75) = happyShift action_39
action_219 (77) = happyShift action_40
action_219 (82) = happyShift action_41
action_219 (83) = happyShift action_42
action_219 (84) = happyShift action_43
action_219 (85) = happyShift action_44
action_219 (86) = happyShift action_45
action_219 (89) = happyShift action_46
action_219 (90) = happyShift action_47
action_219 (91) = happyShift action_25
action_219 (27) = happyGoto action_30
action_219 (46) = happyGoto action_31
action_219 (48) = happyGoto action_32
action_219 (49) = happyGoto action_33
action_219 (50) = happyGoto action_225
action_219 _ = happyFail (happyExpListPerState 219)

action_220 _ = happyReduce_48

action_221 (52) = happyShift action_35
action_221 (60) = happyShift action_36
action_221 (61) = happyShift action_37
action_221 (69) = happyShift action_38
action_221 (75) = happyShift action_39
action_221 (77) = happyShift action_40
action_221 (82) = happyShift action_41
action_221 (83) = happyShift action_42
action_221 (84) = happyShift action_43
action_221 (85) = happyShift action_44
action_221 (86) = happyShift action_45
action_221 (89) = happyShift action_46
action_221 (90) = happyShift action_47
action_221 (91) = happyShift action_25
action_221 (27) = happyGoto action_30
action_221 (46) = happyGoto action_224
action_221 (48) = happyGoto action_32
action_221 (49) = happyGoto action_33
action_221 _ = happyFail (happyExpListPerState 221)

action_222 _ = happyReduce_42

action_223 _ = happyReduce_30

action_224 _ = happyReduce_49

action_225 _ = happyReduce_63

action_226 (52) = happyShift action_35
action_226 (60) = happyShift action_36
action_226 (61) = happyShift action_37
action_226 (69) = happyShift action_38
action_226 (75) = happyShift action_39
action_226 (77) = happyShift action_40
action_226 (82) = happyShift action_41
action_226 (83) = happyShift action_42
action_226 (84) = happyShift action_43
action_226 (85) = happyShift action_44
action_226 (86) = happyShift action_45
action_226 (89) = happyShift action_46
action_226 (90) = happyShift action_47
action_226 (91) = happyShift action_25
action_226 (27) = happyGoto action_30
action_226 (46) = happyGoto action_31
action_226 (48) = happyGoto action_32
action_226 (49) = happyGoto action_33
action_226 (50) = happyGoto action_234
action_226 _ = happyFail (happyExpListPerState 226)

action_227 (53) = happyShift action_233
action_227 _ = happyFail (happyExpListPerState 227)

action_228 (87) = happyShift action_232
action_228 _ = happyFail (happyExpListPerState 228)

action_229 _ = happyReduce_62

action_230 _ = happyReduce_85

action_231 _ = happyReduce_83

action_232 (52) = happyShift action_35
action_232 (60) = happyShift action_36
action_232 (61) = happyShift action_37
action_232 (69) = happyShift action_38
action_232 (75) = happyShift action_39
action_232 (77) = happyShift action_40
action_232 (82) = happyShift action_41
action_232 (83) = happyShift action_42
action_232 (84) = happyShift action_43
action_232 (85) = happyShift action_44
action_232 (86) = happyShift action_45
action_232 (89) = happyShift action_46
action_232 (90) = happyShift action_47
action_232 (91) = happyShift action_25
action_232 (27) = happyGoto action_30
action_232 (46) = happyGoto action_31
action_232 (48) = happyGoto action_32
action_232 (49) = happyGoto action_33
action_232 (50) = happyGoto action_236
action_232 _ = happyFail (happyExpListPerState 232)

action_233 (87) = happyShift action_235
action_233 _ = happyFail (happyExpListPerState 233)

action_234 _ = happyReduce_67

action_235 (52) = happyShift action_35
action_235 (60) = happyShift action_36
action_235 (61) = happyShift action_37
action_235 (69) = happyShift action_38
action_235 (75) = happyShift action_39
action_235 (77) = happyShift action_40
action_235 (82) = happyShift action_41
action_235 (83) = happyShift action_42
action_235 (84) = happyShift action_43
action_235 (85) = happyShift action_44
action_235 (86) = happyShift action_45
action_235 (89) = happyShift action_46
action_235 (90) = happyShift action_47
action_235 (91) = happyShift action_25
action_235 (27) = happyGoto action_30
action_235 (46) = happyGoto action_31
action_235 (48) = happyGoto action_32
action_235 (49) = happyGoto action_33
action_235 (50) = happyGoto action_237
action_235 _ = happyFail (happyExpListPerState 235)

action_236 _ = happyReduce_68

action_237 _ = happyReduce_69

happyReduce_24 = happySpecReduce_1  27 happyReduction_24
happyReduction_24 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn27
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.VarIdent (tokenText happy_var_1))
	)
happyReduction_24 _  = notHappyAtAll 

happyReduce_25 = happySpecReduce_1  28 happyReduction_25
happyReduction_25 (HappyAbsSyn29  happy_var_1)
	 =  HappyAbsSyn28
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AProgram (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_25 _  = notHappyAtAll 

happyReduce_26 = happySpecReduce_0  29 happyReduction_26
happyReduction_26  =  HappyAbsSyn29
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_27 = happySpecReduce_2  29 happyReduction_27
happyReduction_27 (HappyAbsSyn29  happy_var_2)
	(HappyAbsSyn30  happy_var_1)
	 =  HappyAbsSyn29
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_27 _ _  = notHappyAtAll 

happyReduce_28 = happySpecReduce_1  30 happyReduction_28
happyReduction_28 (HappyAbsSyn31  happy_var_1)
	 =  HappyAbsSyn30
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitModule (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_28 _  = notHappyAtAll 

happyReduce_29 = happySpecReduce_1  30 happyReduction_29
happyReduction_29 (HappyAbsSyn37  happy_var_1)
	 =  HappyAbsSyn30
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.UnitTelescope (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_29 _  = notHappyAtAll 

happyReduce_30 = happyReduce 7 31 happyReduction_30
happyReduction_30 ((HappyAbsSyn43  happy_var_7) `HappyStk`
	(HappyAbsSyn41  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	(HappyAbsSyn33  happy_var_3) `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn31
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AModule (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_31 = happySpecReduce_3  32 happyReduction_31
happyReduction_31 (HappyAbsSyn34  happy_var_3)
	(HappyAbsSyn27  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn32
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnInclude (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3))
	)
happyReduction_31 _ _ _  = notHappyAtAll 

happyReduce_32 = happySpecReduce_0  33 happyReduction_32
happyReduction_32  =  HappyAbsSyn33
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_33 = happySpecReduce_2  33 happyReduction_33
happyReduction_33 (HappyAbsSyn33  happy_var_2)
	(HappyAbsSyn32  happy_var_1)
	 =  HappyAbsSyn33
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_33 _ _  = notHappyAtAll 

happyReduce_34 = happySpecReduce_0  34 happyReduction_34
happyReduction_34  =  HappyAbsSyn34
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoRefinement Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_35 = happyReduce 4 34 happyReduction_35
happyReduction_35 (_ `HappyStk`
	(HappyAbsSyn36  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn34
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.ARefinement (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_36 = happySpecReduce_3  35 happyReduction_36
happyReduction_36 (HappyAbsSyn46  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn35
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AFixed (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_36 _ _ _  = notHappyAtAll 

happyReduce_37 = happySpecReduce_0  36 happyReduction_37
happyReduction_37  =  HappyAbsSyn36
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_38 = happySpecReduce_1  36 happyReduction_38
happyReduction_38 (HappyAbsSyn35  happy_var_1)
	 =  HappyAbsSyn36
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_38 _  = notHappyAtAll 

happyReduce_39 = happySpecReduce_3  36 happyReduction_39
happyReduction_39 (HappyAbsSyn36  happy_var_3)
	_
	(HappyAbsSyn35  happy_var_1)
	 =  HappyAbsSyn36
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_39 _ _ _  = notHappyAtAll 

happyReduce_40 = happyReduce 5 37 happyReduction_40
happyReduction_40 (_ `HappyStk`
	(HappyAbsSyn39  happy_var_4) `HappyStk`
	(HappyAbsSyn33  happy_var_3) `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn37
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.ATelescope (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_41 = happyReduce 5 38 happyReduction_41
happyReduction_41 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn38
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AParam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_42 = happyReduce 7 38 happyReduction_42
happyReduction_42 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn38
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AManifest (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_43 = happySpecReduce_0  39 happyReduction_43
happyReduction_43  =  HappyAbsSyn39
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_44 = happySpecReduce_2  39 happyReduction_44
happyReduction_44 (HappyAbsSyn39  happy_var_2)
	(HappyAbsSyn38  happy_var_1)
	 =  HappyAbsSyn39
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_44 _ _  = notHappyAtAll 

happyReduce_45 = happySpecReduce_2  40 happyReduction_45
happyReduction_45 (HappyAbsSyn27  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn40
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.AnImport (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_45 _ _  = notHappyAtAll 

happyReduce_46 = happySpecReduce_0  41 happyReduction_46
happyReduction_46  =  HappyAbsSyn41
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_47 = happySpecReduce_3  41 happyReduction_47
happyReduction_47 (HappyAbsSyn41  happy_var_3)
	_
	(HappyAbsSyn40  happy_var_1)
	 =  HappyAbsSyn41
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_47 _ _ _  = notHappyAtAll 

happyReduce_48 = happyReduce 7 42 happyReduction_48
happyReduction_48 ((HappyAbsSyn46  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn44  happy_var_3) `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_49 = happyReduce 8 42 happyReduction_49
happyReduction_49 ((HappyAbsSyn46  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn44  happy_var_4) `HappyStk`
	(HappyAbsSyn27  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclPrivateDef (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_50 = happyReduce 6 42 happyReduction_50
happyReduction_50 (_ `HappyStk`
	(HappyAbsSyn43  happy_var_5) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn27  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclNamespace (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_5))
	) `HappyStk` happyRest

happyReduce_51 = happySpecReduce_2  42 happyReduction_51
happyReduction_51 (HappyAbsSyn27  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclOpen (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_51 _ _  = notHappyAtAll 

happyReduce_52 = happyReduce 4 42 happyReduction_52
happyReduction_52 ((HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCheck (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_53 = happySpecReduce_2  42 happyReduction_53
happyReduction_53 (HappyAbsSyn46  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn42
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DeclCompute (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_53 _ _  = notHappyAtAll 

happyReduce_54 = happySpecReduce_0  43 happyReduction_54
happyReduction_54  =  HappyAbsSyn43
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_55 = happySpecReduce_1  43 happyReduction_55
happyReduction_55 (HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn43
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_55 _  = notHappyAtAll 

happyReduce_56 = happySpecReduce_3  43 happyReduction_56
happyReduction_56 (HappyAbsSyn43  happy_var_3)
	_
	(HappyAbsSyn42  happy_var_1)
	 =  HappyAbsSyn43
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_56 _ _ _  = notHappyAtAll 

happyReduce_57 = happySpecReduce_0  44 happyReduction_57
happyReduction_57  =  HappyAbsSyn44
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, Language.MLTT.Syntax.Abs.NoDischarge Language.MLTT.Syntax.Abs.BNFC'NoPosition)
	)

happyReduce_58 = happyReduce 4 44 happyReduction_58
happyReduction_58 (_ `HappyStk`
	(HappyAbsSyn45  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn44
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.DischargeOver (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_59 = happySpecReduce_0  45 happyReduction_59
happyReduction_59  =  HappyAbsSyn45
		 ((Language.MLTT.Syntax.Abs.BNFC'NoPosition, [])
	)

happyReduce_60 = happySpecReduce_1  45 happyReduction_60
happyReduction_60 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, (:[]) (snd happy_var_1))
	)
happyReduction_60 _  = notHappyAtAll 

happyReduce_61 = happySpecReduce_3  45 happyReduction_61
happyReduction_61 (HappyAbsSyn45  happy_var_3)
	_
	(HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn45
		 ((fst happy_var_1, (:) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_61 _ _ _  = notHappyAtAll 

happyReduce_62 = happyReduce 8 46 happyReduction_62
happyReduction_62 ((HappyAbsSyn47  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pi (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_63 = happyReduce 8 46 happyReduction_63
happyReduction_63 ((HappyAbsSyn47  happy_var_8) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Sigma (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_8))
	) `HappyStk` happyRest

happyReduce_64 = happyReduce 4 46 happyReduction_64
happyReduction_64 ((HappyAbsSyn47  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Lam (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_65 = happyReduce 6 46 happyReduction_65
happyReduction_65 ((HappyAbsSyn47  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Let (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4) (snd happy_var_6))
	) `HappyStk` happyRest

happyReduce_66 = happyReduce 4 46 happyReduction_66
happyReduction_66 ((HappyAbsSyn47  happy_var_4) `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	(HappyAbsSyn51  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.lamMulti (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_3) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_67 = happyReduce 9 46 happyReduction_67
happyReduction_67 ((HappyAbsSyn47  happy_var_9) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_6) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_4) `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.piTwo (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_6) (snd happy_var_9))
	) `HappyStk` happyRest

happyReduce_68 = happyReduce 10 46 happyReduction_68
happyReduction_68 ((HappyAbsSyn47  happy_var_10) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_5) `HappyStk`
	(HappyAbsSyn51  happy_var_4) `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.piThree (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_5) (snd happy_var_7) (snd happy_var_10))
	) `HappyStk` happyRest

happyReduce_69 = happyReduce 11 46 happyReduction_69
happyReduction_69 ((HappyAbsSyn47  happy_var_11) `HappyStk`
	_ `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_8) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_6) `HappyStk`
	(HappyAbsSyn51  happy_var_5) `HappyStk`
	(HappyAbsSyn51  happy_var_4) `HappyStk`
	(HappyAbsSyn51  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.piFour (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_4) (snd happy_var_5) (snd happy_var_6) (snd happy_var_8) (snd happy_var_11))
	) `HappyStk` happyRest

happyReduce_70 = happySpecReduce_3  46 happyReduction_70
happyReduction_70 (HappyAbsSyn46  happy_var_3)
	_
	(HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Arrow (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_70 _ _ _  = notHappyAtAll 

happyReduce_71 = happySpecReduce_3  46 happyReduction_71
happyReduction_71 (HappyAbsSyn46  happy_var_3)
	_
	(HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Product (fst happy_var_1) (snd happy_var_1) (snd happy_var_3))
	)
happyReduction_71 _ _ _  = notHappyAtAll 

happyReduce_72 = happySpecReduce_1  46 happyReduction_72
happyReduction_72 (HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_72 _  = notHappyAtAll 

happyReduce_73 = happySpecReduce_2  47 happyReduction_73
happyReduction_73 (HappyAbsSyn46  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn47
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.lamRestDone (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_73 _ _  = notHappyAtAll 

happyReduce_74 = happySpecReduce_2  47 happyReduction_74
happyReduction_74 (HappyAbsSyn47  happy_var_2)
	(HappyAbsSyn51  happy_var_1)
	 =  HappyAbsSyn47
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.lamRestMore (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_74 _ _  = notHappyAtAll 

happyReduce_75 = happySpecReduce_2  48 happyReduction_75
happyReduction_75 (HappyAbsSyn46  happy_var_2)
	(HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.App (fst happy_var_1) (snd happy_var_1) (snd happy_var_2))
	)
happyReduction_75 _ _  = notHappyAtAll 

happyReduce_76 = happySpecReduce_1  48 happyReduction_76
happyReduction_76 (HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, (snd happy_var_1))
	)
happyReduction_76 _  = notHappyAtAll 

happyReduce_77 = happySpecReduce_2  49 happyReduction_77
happyReduction_77 (HappyAbsSyn46  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.First (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_77 _ _  = notHappyAtAll 

happyReduce_78 = happySpecReduce_2  49 happyReduction_78
happyReduction_78 (HappyAbsSyn46  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Second (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2))
	)
happyReduction_78 _ _  = notHappyAtAll 

happyReduce_79 = happySpecReduce_1  49 happyReduction_79
happyReduction_79 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Universe (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_79 _  = notHappyAtAll 

happyReduce_80 = happySpecReduce_1  49 happyReduction_80
happyReduction_80 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_80 _  = notHappyAtAll 

happyReduce_81 = happySpecReduce_1  49 happyReduction_81
happyReduction_81 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.UnitVal (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_81 _  = notHappyAtAll 

happyReduce_82 = happySpecReduce_1  49 happyReduction_82
happyReduction_82 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn46
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.Var (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_82 _  = notHappyAtAll 

happyReduce_83 = happyReduce 8 49 happyReduction_83
happyReduction_83 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.IdType (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_84 = happyReduce 4 49 happyReduction_84
happyReduction_84 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Refl (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3))
	) `HappyStk` happyRest

happyReduce_85 = happyReduce 8 49 happyReduction_85
happyReduction_85 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_7) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_5) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_3) `HappyStk`
	_ `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.J (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_3) (snd happy_var_5) (snd happy_var_7))
	) `HappyStk` happyRest

happyReduce_86 = happyReduce 5 49 happyReduction_86
happyReduction_86 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Pair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_87 = happyReduce 5 49 happyReduction_87
happyReduction_87 (_ `HappyStk`
	(HappyAbsSyn46  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn46  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.Ann (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyReduce_88 = happySpecReduce_3  49 happyReduction_88
happyReduction_88 _
	(HappyAbsSyn46  happy_var_2)
	(HappyTerminal happy_var_1)
	 =  HappyAbsSyn46
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), (snd happy_var_2))
	)
happyReduction_88 _ _ _  = notHappyAtAll 

happyReduce_89 = happySpecReduce_1  50 happyReduction_89
happyReduction_89 (HappyAbsSyn46  happy_var_1)
	 =  HappyAbsSyn47
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.AScopedTerm (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_89 _  = notHappyAtAll 

happyReduce_90 = happySpecReduce_1  51 happyReduction_90
happyReduction_90 (HappyTerminal happy_var_1)
	 =  HappyAbsSyn51
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternWildcard (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)))
	)
happyReduction_90 _  = notHappyAtAll 

happyReduce_91 = happySpecReduce_1  51 happyReduction_91
happyReduction_91 (HappyAbsSyn27  happy_var_1)
	 =  HappyAbsSyn51
		 ((fst happy_var_1, Language.MLTT.Syntax.Abs.PatternVar (fst happy_var_1) (snd happy_var_1))
	)
happyReduction_91 _  = notHappyAtAll 

happyReduce_92 = happyReduce 5 51 happyReduction_92
happyReduction_92 (_ `HappyStk`
	(HappyAbsSyn51  happy_var_4) `HappyStk`
	_ `HappyStk`
	(HappyAbsSyn51  happy_var_2) `HappyStk`
	(HappyTerminal happy_var_1) `HappyStk`
	happyRest)
	 = HappyAbsSyn51
		 ((uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1), Language.MLTT.Syntax.Abs.PatternPair (uncurry Language.MLTT.Syntax.Abs.BNFC'Position (tokenLineCol happy_var_1)) (snd happy_var_2) (snd happy_var_4))
	) `HappyStk` happyRest

happyNewToken action sts stk [] =
	action 92 92 notHappyAtAll (HappyState action) sts stk []

happyNewToken action sts stk (tk:tks) =
	let cont i = action i i tk (HappyState action) sts stk tks in
	case tk of {
	PT _ (TS _ 1) -> cont 52;
	PT _ (TS _ 2) -> cont 53;
	PT _ (TS _ 3) -> cont 54;
	PT _ (TS _ 4) -> cont 55;
	PT _ (TS _ 5) -> cont 56;
	PT _ (TS _ 6) -> cont 57;
	PT _ (TS _ 7) -> cont 58;
	PT _ (TS _ 8) -> cont 59;
	PT _ (TS _ 9) -> cont 60;
	PT _ (TS _ 10) -> cont 61;
	PT _ (TS _ 11) -> cont 62;
	PT _ (TS _ 12) -> cont 63;
	PT _ (TS _ 13) -> cont 64;
	PT _ (TS _ 14) -> cont 65;
	PT _ (TS _ 15) -> cont 66;
	PT _ (TS _ 16) -> cont 67;
	PT _ (TS _ 17) -> cont 68;
	PT _ (TS _ 18) -> cont 69;
	PT _ (TS _ 19) -> cont 70;
	PT _ (TS _ 20) -> cont 71;
	PT _ (TS _ 21) -> cont 72;
	PT _ (TS _ 22) -> cont 73;
	PT _ (TS _ 23) -> cont 74;
	PT _ (TS _ 24) -> cont 75;
	PT _ (TS _ 25) -> cont 76;
	PT _ (TS _ 26) -> cont 77;
	PT _ (TS _ 27) -> cont 78;
	PT _ (TS _ 28) -> cont 79;
	PT _ (TS _ 29) -> cont 80;
	PT _ (TS _ 30) -> cont 81;
	PT _ (TS _ 31) -> cont 82;
	PT _ (TS _ 32) -> cont 83;
	PT _ (TS _ 33) -> cont 84;
	PT _ (TS _ 34) -> cont 85;
	PT _ (TS _ 35) -> cont 86;
	PT _ (TS _ 36) -> cont 87;
	PT _ (TS _ 37) -> cont 88;
	PT _ (TS _ 38) -> cont 89;
	PT _ (TS _ 39) -> cont 90;
	PT _ (T_VarIdent _) -> cont 91;
	_ -> happyError' ((tk:tks), [])
	}

happyError_ explist 92 tk tks = happyError' (tks, explist)
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
 happySomeParser = happyThen (happyParse action_0 tks) (\x -> case x of {HappyAbsSyn28 z -> happyReturn z; _other -> notHappyAtAll })

pListUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_1 tks) (\x -> case x of {HappyAbsSyn29 z -> happyReturn z; _other -> notHappyAtAll })

pUnit_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_2 tks) (\x -> case x of {HappyAbsSyn30 z -> happyReturn z; _other -> notHappyAtAll })

pModule_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_3 tks) (\x -> case x of {HappyAbsSyn31 z -> happyReturn z; _other -> notHappyAtAll })

pInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_4 tks) (\x -> case x of {HappyAbsSyn32 z -> happyReturn z; _other -> notHappyAtAll })

pListInclude_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_5 tks) (\x -> case x of {HappyAbsSyn33 z -> happyReturn z; _other -> notHappyAtAll })

pRefinement_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_6 tks) (\x -> case x of {HappyAbsSyn34 z -> happyReturn z; _other -> notHappyAtAll })

pFixed_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_7 tks) (\x -> case x of {HappyAbsSyn35 z -> happyReturn z; _other -> notHappyAtAll })

pListFixed_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_8 tks) (\x -> case x of {HappyAbsSyn36 z -> happyReturn z; _other -> notHappyAtAll })

pTelescopeDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_9 tks) (\x -> case x of {HappyAbsSyn37 z -> happyReturn z; _other -> notHappyAtAll })

pParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_10 tks) (\x -> case x of {HappyAbsSyn38 z -> happyReturn z; _other -> notHappyAtAll })

pListParam_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_11 tks) (\x -> case x of {HappyAbsSyn39 z -> happyReturn z; _other -> notHappyAtAll })

pImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_12 tks) (\x -> case x of {HappyAbsSyn40 z -> happyReturn z; _other -> notHappyAtAll })

pListImport_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_13 tks) (\x -> case x of {HappyAbsSyn41 z -> happyReturn z; _other -> notHappyAtAll })

pDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_14 tks) (\x -> case x of {HappyAbsSyn42 z -> happyReturn z; _other -> notHappyAtAll })

pListDecl_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_15 tks) (\x -> case x of {HappyAbsSyn43 z -> happyReturn z; _other -> notHappyAtAll })

pDischarge_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_16 tks) (\x -> case x of {HappyAbsSyn44 z -> happyReturn z; _other -> notHappyAtAll })

pListVarIdent_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_17 tks) (\x -> case x of {HappyAbsSyn45 z -> happyReturn z; _other -> notHappyAtAll })

pTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_18 tks) (\x -> case x of {HappyAbsSyn46 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm9_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_19 tks) (\x -> case x of {HappyAbsSyn47 z -> happyReturn z; _other -> notHappyAtAll })

pTerm1_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_20 tks) (\x -> case x of {HappyAbsSyn46 z -> happyReturn z; _other -> notHappyAtAll })

pTerm2_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_21 tks) (\x -> case x of {HappyAbsSyn46 z -> happyReturn z; _other -> notHappyAtAll })

pScopedTerm_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_22 tks) (\x -> case x of {HappyAbsSyn47 z -> happyReturn z; _other -> notHappyAtAll })

pPattern_internal tks = happySomeParser where
 happySomeParser = happyThen (happyParse action_23 tks) (\x -> case x of {HappyAbsSyn51 z -> happyReturn z; _other -> notHappyAtAll })

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

pListUnit :: [Token] -> Err [Language.MLTT.Syntax.Abs.Unit]
pListUnit = fmap snd . pListUnit_internal

pUnit :: [Token] -> Err Language.MLTT.Syntax.Abs.Unit
pUnit = fmap snd . pUnit_internal

pModule :: [Token] -> Err Language.MLTT.Syntax.Abs.Module
pModule = fmap snd . pModule_internal

pInclude :: [Token] -> Err Language.MLTT.Syntax.Abs.Include
pInclude = fmap snd . pInclude_internal

pListInclude :: [Token] -> Err [Language.MLTT.Syntax.Abs.Include]
pListInclude = fmap snd . pListInclude_internal

pRefinement :: [Token] -> Err Language.MLTT.Syntax.Abs.Refinement
pRefinement = fmap snd . pRefinement_internal

pFixed :: [Token] -> Err Language.MLTT.Syntax.Abs.Fixed
pFixed = fmap snd . pFixed_internal

pListFixed :: [Token] -> Err [Language.MLTT.Syntax.Abs.Fixed]
pListFixed = fmap snd . pListFixed_internal

pTelescopeDecl :: [Token] -> Err Language.MLTT.Syntax.Abs.TelescopeDecl
pTelescopeDecl = fmap snd . pTelescopeDecl_internal

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

pScopedTerm9 :: [Token] -> Err Language.MLTT.Syntax.Abs.ScopedTerm
pScopedTerm9 = fmap snd . pScopedTerm9_internal

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
