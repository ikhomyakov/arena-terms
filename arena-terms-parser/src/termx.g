--
-- Copyright (c) 2004-2025 Andrey Dadakov & Igor Khomyakov. All rights reserved.
--
-- Redistribution and use in source and binary forms, with or without
-- modification, are permitted provided that the following conditions are met:
--
-- 1) Redistributions of source code must retain the above copyright notice,
-- this list of conditions and the following disclaimer.
-- 2) Redistributions of source code with modification must include a notice
-- that the code was modified.
-- 3) Neither the names of the authors nor the names of their contributors may
-- be used to endorse or promote products derived from this software without
-- specific prior written permission.
--
-- THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
-- AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
-- IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
-- ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
-- LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
-- CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
-- SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
-- INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
-- CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
-- ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
-- POSSIBILITY OF SUCH DAMAGE.
--
term1:      Term -> Expr
term2:      Term -> Expr .
term3:      Term ->
term4:      Term -> .

func:       Expr -> func Seq )
list:       Expr -> [ Seq ]
nil:        Expr -> [ ]
list2:      Expr -> [ Seq | Expr ]
tuple:      Expr -> ( Seq )
unit:       Expr -> ( )
atom:       Expr -> atom
var:        Expr -> var
int:        Expr -> int
real:       Expr -> real
date:       Expr -> date
str:        Expr -> str
bin:        Expr -> bin

infix1:      Expr -> Expr atomOper Expr
infix2:      Expr -> Expr funcOper Seq ) Expr
prefix1:     Expr -> atomOper Expr
prefix2:     Expr -> funcOper Seq ) Expr
postfix1:    Expr -> Expr atomOper
postfix2:    Expr -> Expr funcOper Seq )

seq1:       Seq -> BareSeq
seq2:       Seq -> BareSeq ,

bareSeq1:   BareSeq -> Expr
bareSeq2:   BareSeq -> BareSeq , Expr

--
