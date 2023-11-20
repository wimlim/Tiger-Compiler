#include "tiger/absyn/absyn.h"
#include "tiger/semant/semant.h"
namespace {
  template <typename T, typename ProcessField>
  static T* make_list(sym::Table<type::Ty>* tenv, absyn::FieldList* fields, err::ErrorMsg* errormsg, ProcessField process) {
      if (fields == nullptr) return nullptr;

      T* ans = new T();

      const std::list<absyn::Field *> * field_list = &fields->GetList();
      for (auto iter = field_list->begin(); iter != field_list->end(); iter++) {
        type::Ty* ty = tenv->Look((*iter)->typ_);
        
        if (ty == nullptr) {
          errormsg->Error((*iter)->pos_, "undefined type %s", (*iter)->typ_->Name().c_str());
          continue;
        }
        
        process(ans, *iter, ty);
      }
      return ans;
  }

  static type::TyList* make_formal_tylist(sym::Table<type::Ty>* tenv, absyn::FieldList* params, err::ErrorMsg *errormsg) {
      return make_list<type::TyList>(tenv, params, errormsg, [](type::TyList* list, absyn::Field* field, type::Ty* ty) {
          list->Append(ty->ActualTy());
      });
  }

  static type::FieldList* make_fieldlist(sym::Table<type::Ty>* tenv, absyn::FieldList* fields, err::ErrorMsg* errormsg) {
      return make_list<type::FieldList>(tenv, fields, errormsg, [](type::FieldList* list, absyn::Field* field, type::Ty* ty) {
          list->Append(new type::Field(field->name_, ty));
      });
  }
}

namespace absyn {

void AbsynTree::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                           err::ErrorMsg *errormsg) const {
  root_->SemAnalyze(venv, tenv, 0, errormsg);
}

type::Ty *SimpleVar::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                                int labelcount, err::ErrorMsg *errormsg) const {
  env::EnvEntry *entry = venv->Look(sym_);
  if (entry && typeid(*entry) == typeid(env::VarEntry)) {
    return static_cast<env::VarEntry *>(entry)->ty_->ActualTy();
  } else {
    errormsg->Error(pos_, "undefined variable %s", sym_->Name().c_str());
    return type::VoidTy::Instance();
  }
}

type::Ty *FieldVar::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                               int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *ty = var_->SemAnalyze(venv, tenv, labelcount, errormsg)->ActualTy();

  if (typeid(*ty) == typeid(type::RecordTy)) {
    type::RecordTy *record_ty = static_cast<type::RecordTy *>(ty);
    const auto &field_list = record_ty->fields_->GetList();

    type::Ty *field_ty = nullptr;
    for (auto &field : field_list) {
      if (field->name_->Name() == sym_->Name()) {
        field_ty = field->ty_->ActualTy();
        break;
      }
    }
    if (field_ty) {
      return field_ty;
    } else {
      errormsg->Error(pos_, "field %s doesn't exist", sym_->Name().c_str());
      return type::VoidTy::Instance();
    }
  } else {
    errormsg->Error(pos_, "not a record type");
    return type::VoidTy::Instance();
  }
}

type::Ty *SubscriptVar::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   int labelcount,
                                   err::ErrorMsg *errormsg) const {
  type::Ty *subscript_ty = subscript_->SemAnalyze(venv, tenv, labelcount, errormsg)->ActualTy();
  if (typeid(*subscript_ty) != typeid(type::IntTy)) {
    errormsg->Error(pos_, "integer required");
    return type::VoidTy::Instance();
  }

  type::Ty *var_ty = var_->SemAnalyze(venv, tenv, labelcount, errormsg)->ActualTy();
  if (typeid(*var_ty) == typeid(type::ArrayTy)) {
    type::ArrayTy *array_ty = static_cast<type::ArrayTy *>(var_ty);
    return array_ty->ty_->ActualTy();
  } else {
    errormsg->Error(pos_, "array type required");
    return type::VoidTy::Instance();
  }
}

type::Ty *VarExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  return var_->SemAnalyze(venv, tenv, labelcount, errormsg);
}

type::Ty *NilExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  return type::NilTy::Instance();
}

type::Ty *IntExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  return type::IntTy::Instance();
}

type::Ty *StringExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                                int labelcount, err::ErrorMsg *errormsg) const {
  return type::StringTy::Instance();
}

type::Ty *CallExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                              int labelcount, err::ErrorMsg *errormsg) const {
  if (func_ == nullptr) {
    errormsg->Error(pos_, "func_ is null");
  }
  env::EnvEntry *entry = venv->Look(func_);
  if (entry && typeid(*entry) == typeid(env::FunEntry)) {
    env::FunEntry *fun_entry = static_cast<env::FunEntry *>(entry);
    type::TyList *formal_tys = fun_entry->formals_;
    const auto &field_list = args_->GetList();
    const auto &ty_list = formal_tys->GetList();
    if (field_list.size() < ty_list.size()) {
      errormsg->Error(pos_, "too few params in function %s", func_->Name().c_str());
    } else if (field_list.size() > ty_list.size()) {
      errormsg->Error(pos_, "too many params in function %s", func_->Name().c_str());
    }

    auto it1 = field_list.begin();
    auto it2 = ty_list.begin();
    for (; it1 != field_list.end() && it2 != ty_list.end(); ++it1, ++it2) {
      type::Ty *arg_ty = (*it1)->SemAnalyze(venv, tenv, labelcount, errormsg)->ActualTy();
      if (!arg_ty->IsSameType(*it2)) {
        errormsg->Error(pos_, "para type mismatch");
      }
    }
    return fun_entry->result_;
  } else {
    errormsg->Error(pos_, "undefined function %s", func_->Name().c_str());
    return type::VoidTy::Instance();
  }
}

type::Ty *OpExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                            int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *left_ty = left_->SemAnalyze(venv, tenv, labelcount, errormsg);
  type::Ty *right_ty = right_->SemAnalyze(venv, tenv, labelcount, errormsg);
  switch (oper_) {
    case absyn::PLUS_OP:
    case absyn::MINUS_OP:
    case absyn::TIMES_OP:
    case absyn::DIVIDE_OP:
      if (typeid(*left_ty) != typeid(type::IntTy)) {
        errormsg->Error(left_->pos_, "integer required");
      }
      if (typeid(*right_ty) != typeid(type::IntTy)) {
        errormsg->Error(right_->pos_, "integer required");
      }
      return type::IntTy::Instance();
    default:
      if (typeid(*left_ty) != typeid(*right_ty)) {
        errormsg->Error(pos_, "same type required");
      }
      return type::VoidTy::Instance();
  }
}

type::Ty *RecordExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                                int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *ty = tenv->Look(typ_);
  if (ty) {
    ty = ty->ActualTy();
    if (typeid(*ty) != typeid(type::RecordTy)) {
      errormsg->Error(pos_, "not record type");
      return ty;
    } else {
      type::RecordTy *record_ty = static_cast<type::RecordTy *>(ty);
      const auto &field_list = record_ty->fields_->GetList();
      const auto &exp_list = fields_->GetList();

      if (field_list.size() != exp_list.size()) {
        errormsg->Error(pos_, "record type mismatch");
        return ty;
      }

      for (auto &exp : exp_list) {
        for (auto &field : field_list) {
          if (field->name_->Name() == exp->name_->Name()) {
            type::Ty *field_ty = field->ty_->ActualTy();
            type::Ty *exp_ty = exp->exp_->SemAnalyze(venv, tenv, labelcount, errormsg)->ActualTy();
            if (!field_ty->IsSameType(exp_ty)) {
              errormsg->Error(pos_, "unmatched assign exp");
            }
            break;
          }
        }
      }
      return ty;
    }

  } else {
    errormsg->Error(pos_, "undefined type %s", typ_->Name().c_str());
    return type::VoidTy::Instance();
  }

}

type::Ty *SeqExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  const auto &list = seq_->GetList();
  type::Ty *result = type::VoidTy::Instance();
  for (auto &exp : list) {
    result = exp->SemAnalyze(venv, tenv, labelcount, errormsg);
  }
  return result;
}

type::Ty *AssignExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                                int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *var_ty = var_->SemAnalyze(venv, tenv, labelcount, errormsg);
  type::Ty *exp_ty = exp_->SemAnalyze(venv, tenv, labelcount, errormsg);

  if (typeid(*var_) == typeid(SimpleVar)) {
    SimpleVar *svar = static_cast<SimpleVar *>(var_);
    env::EnvEntry *entry = venv->Look(svar->sym_);
    if (entry->readonly_) {
      errormsg->Error(pos_, "loop variable can't be assigned");
    }
  }
  if (typeid(*var_ty) != typeid(*exp_ty)) {
    errormsg->Error(pos_, "unmatched assign exp");
  }
  return type::VoidTy::Instance();
}

type::Ty *IfExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                            int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *test_ty = test_->SemAnalyze(venv, tenv, labelcount, errormsg);
  // if (typeid(*test_ty) != typeid(type::IntTy)) {
  //   errormsg->Error(pos_, "integer required");
  // }
  type::Ty *then_ty = then_->SemAnalyze(venv, tenv, labelcount, errormsg);
  if (elsee_) {
    type::Ty *else_ty = elsee_->SemAnalyze(venv, tenv, labelcount, errormsg);
    if (!then_ty->IsSameType(else_ty)) {
      errormsg->Error(pos_, "then exp and else exp type mismatch");
    }
    return then_ty->ActualTy();
  } else {
    if (typeid(*then_ty) != typeid(type::VoidTy)) {
      errormsg->Error(pos_, "if-then exp's body must produce no value");
    }
    return type::VoidTy::Instance();
  }
}

type::Ty *WhileExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                               int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *test_ty = test_->SemAnalyze(venv, tenv, labelcount, errormsg);
  if (typeid(*test_ty) != typeid(type::IntTy)) {
    errormsg->Error(pos_, "integer required");
  }
  if (body_) {
    type::Ty *body_ty = body_->SemAnalyze(venv, tenv, labelcount + 1, errormsg);
    if (typeid(*body_ty) != typeid(type::VoidTy)) {
      errormsg->Error(pos_, "while body must produce no value");
    }
  }
  return type::VoidTy::Instance();
}

type::Ty *ForExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *low_ty = lo_->SemAnalyze(venv, tenv, labelcount, errormsg);
  type::Ty *high_ty = hi_->SemAnalyze(venv, tenv, labelcount, errormsg);

  if (typeid(*low_ty) != typeid(type::IntTy)) {
    errormsg->Error(lo_->pos_, "for exp's range type is not integer");
  }
  if (typeid(*high_ty) != typeid(type::IntTy)) {
    errormsg->Error(hi_->pos_, "for exp's range type is not integer");
  }
  if (body_) {
    venv->BeginScope();
    venv->Enter(var_, new env::VarEntry(type::IntTy::Instance(), true));
    type::Ty *body_ty = body_->SemAnalyze(venv, tenv, labelcount + 1, errormsg);
    if (typeid(*body_ty) != typeid(type::VoidTy)) {
      errormsg->Error(pos_, "for body must produce no value");
    }
    venv->EndScope();
  }
  return type::VoidTy::Instance();
}

type::Ty *BreakExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                               int labelcount, err::ErrorMsg *errormsg) const {
  if (labelcount == 0) {
    errormsg->Error(pos_, "break is not inside any loop");
  }
  return type::VoidTy::Instance();
}

type::Ty *LetExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  venv->BeginScope();
  tenv->BeginScope();
  const auto &list = decs_->GetList();
  for (auto &dec : list) {
    dec->SemAnalyze(venv, tenv, labelcount, errormsg);
  }

  type::Ty *result;
  if (!body_) {
    result = type::VoidTy::Instance();
  } else {
    result = body_->SemAnalyze(venv, tenv, labelcount, errormsg);
  }
  return result;
}

type::Ty *ArrayExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                               int labelcount, err::ErrorMsg *errormsg) const {
  type::Ty *ty = tenv->Look(typ_);
  if (ty) {
    ty = ty->ActualTy();
    if (typeid(*ty) != typeid(type::ArrayTy)) {
      errormsg->Error(pos_, "not array type");
      return type::VoidTy::Instance();
    }
    type::ArrayTy *array_ty = static_cast<type::ArrayTy *>(ty);

    type::Ty *size_ty = size_->SemAnalyze(venv, tenv, labelcount, errormsg);
    if (typeid(*size_ty) != typeid(type::IntTy)) {
      errormsg->Error(pos_, "integer required");
    }
    type::Ty *init_ty = init_->SemAnalyze(venv, tenv, labelcount, errormsg);
    if (!init_ty->IsSameType(array_ty->ty_)) {
      errormsg->Error(pos_, "type mismatch");
    }
    return array_ty->ActualTy();
  } else {
    errormsg->Error(pos_, "undefined type %s", typ_->Name().c_str());
    return type::VoidTy::Instance();
  }
}

type::Ty *VoidExp::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                              int labelcount, err::ErrorMsg *errormsg) const {
  return type::VoidTy::Instance();
}

void FunctionDec::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv,
                             int labelcount, err::ErrorMsg *errormsg) const {
  const auto &list = functions_->GetList();
  // first pass
  for (auto &func : list) {
    if (venv->Look(func->name_)) {
      errormsg->Error(pos_, "two functions have the same name");
    }
    type::TyList *formal_tys = func->params_->MakeFormalTyList(tenv, errormsg);
    if (func->result_) {
      type::Ty *result_ty = tenv->Look(func->result_);
      if (result_ty) {
        venv->Enter(func->name_, new env::FunEntry(formal_tys, result_ty));
      } else {
        errormsg->Error(pos_, "undefined type %s", func->result_->Name().c_str());
      }
    } else {
      venv->Enter(func->name_, new env::FunEntry(formal_tys, type::VoidTy::Instance()));
    }
  }
  // second pass
  for (auto &func : list) {
    venv->BeginScope();
    type::TyList *formal_tys = func->params_->MakeFormalTyList(tenv, errormsg);
    const auto &fieldList = func->params_->GetList();
    const auto &tyList = formal_tys->GetList();
    auto it1 = fieldList.begin();
    auto it2 = tyList.begin();
    for (; it1 != fieldList.end() && it2 != tyList.end(); ++it1, ++it2) {
      venv->Enter((*it1)->name_, new env::VarEntry(*it2));
    }

    type::Ty *result_ty = func->body_->SemAnalyze(venv, tenv, labelcount, errormsg);
    env::EnvEntry *entry = venv->Look(func->name_);
    if (entry && typeid(*entry) == typeid(env::FunEntry)) {
      env::FunEntry *fun_entry = static_cast<env::FunEntry *>(entry);
      if (!result_ty->IsSameType(fun_entry->result_)) {
        errormsg->Error(pos_, "procedure returns value");
      }
    }
    venv->EndScope();
  }
}

void VarDec::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv, int labelcount,
                        err::ErrorMsg *errormsg) const {
  if (venv->Look(var_)) {
    errormsg->Error(pos_, "two variables have the same name");
    return;
  }
  type::Ty *init_ty = init_->SemAnalyze(venv, tenv, labelcount, errormsg);
  if (typ_) {
    type::Ty *ty = tenv->Look(typ_);
    if (ty) {
      if (!ty->IsSameType(init_ty)) {
        errormsg->Error(pos_, "type mismatch");
      }
      venv->Enter(var_, new env::VarEntry(ty));
    } else {
      errormsg->Error(pos_, "undefined type %s", typ_->Name().c_str());
    }
  } else {
    if (init_ty->IsSameType(type::NilTy::Instance()) && typeid(*init_ty) != typeid(type::RecordTy)) {
      errormsg->Error(pos_, "init should not be nil without type specified");
    } else {
      venv->Enter(var_, new env::VarEntry(init_ty));
    }
  }
}

void TypeDec::SemAnalyze(env::VEnvPtr venv, env::TEnvPtr tenv, int labelcount,
                         err::ErrorMsg *errormsg) const {
  const auto &list = types_->GetList();
  // first pass
  for (const auto &ty : list) {
    if (tenv->Look(ty->name_)) {
      errormsg->Error(pos_, "two types have the same name");
    } else {
      tenv->Enter(ty->name_, new type::NameTy(ty->name_, nullptr));
    }
  }
  // second pass
  for (const auto &ty : list) {
    type::Ty *ty_ty = tenv->Look(ty->name_);
    type::NameTy *name_ty = static_cast<type::NameTy *>(ty_ty);
    name_ty->ty_ = ty->ty_->SemAnalyze(tenv, errormsg);
  }

  bool loop = false;
  for (const auto &ty : list) {
    type::Ty *ty_ty = tenv->Look(ty->name_);
    type::NameTy *name_ty = static_cast<type::NameTy *>(ty_ty);
    while (typeid(*name_ty->ty_) == typeid(type::NameTy)) {
      name_ty = static_cast<type::NameTy *>(name_ty->ty_);
      if (name_ty->sym_ == ty->name_) {
        loop = true;
        break;
      }
    }
    if (loop) {
      errormsg->Error(pos_, "illegal type cycle");
      break;
    }
  }
}

type::Ty *NameTy::SemAnalyze(env::TEnvPtr tenv, err::ErrorMsg *errormsg) const {
  type::Ty *ty = tenv->Look(name_);
  if (ty) {
    return ty;
  } else {
    errormsg->Error(pos_, "undefined type %s", name_->Name().c_str());
    return type::VoidTy::Instance();
  }
}

type::Ty *RecordTy::SemAnalyze(env::TEnvPtr tenv,
                               err::ErrorMsg *errormsg) const {
  return new type::RecordTy(record_->MakeFieldList(tenv, errormsg));
}

type::Ty *ArrayTy::SemAnalyze(env::TEnvPtr tenv,
                              err::ErrorMsg *errormsg) const {
  type::Ty *ty = tenv->Look(array_);
  if (ty) {
    return new type::ArrayTy(ty);
  } else {
    errormsg->Error(pos_, "undefined type %s", array_->Name().c_str());
    return type::VoidTy::Instance();
  }
}

} // namespace absyn

namespace sem {

void ProgSem::SemAnalyze() {
  FillBaseVEnv();
  FillBaseTEnv();
  absyn_tree_->SemAnalyze(venv_.get(), tenv_.get(), errormsg_.get());
}

} // namespace tr
