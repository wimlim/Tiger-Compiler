# comments handling
解析器初始状态遇到'/&ast;'时，会执行adjust并切换到StartCondition__::COMMENT。
在注释块中，如果遇到'/&ast;'，则comment_level_加一；遇到其他任意符号继续；遇到'&ast;/'时comment_level_减一，comment_level_归零时完成匹配，返回初始状态。

# strings handling
解析器初始状态遇到"时切换到StartCondition__::STR。
在STR块中，分为两种情况。一种是遇到"以外的字符内容，包括'\\\"','\\\\','\\n','\t'和其他字符内容。\\[[:digit:]]{3}匹配三位八进制转义字符，\\[ \n\t\f]+\\匹配空白符和换行符；另一种是遇到",这里我们通过setmatched()将string_buf_保存到lex已适配的text，再返回初始状态。

# error handling
将所有合法匹配放在前面，如果前面不存在匹配内容，则最后遇到任何内容都发出错误消息。
. {adjust(); errormsg_->Error(errormsg_->tok_pos_, "illegal token");}

# end-of-line handling
一般情况下通过<code>\n {adjust(); errormsg_->Newline();}<code>处理换行，string和comment中也对\n有专门规则处理。
