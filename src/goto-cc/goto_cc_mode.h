/*******************************************************************\

Module: Command line interpretation for goto-cc.

Author: CM Wintersteiger

Date: June 2006

\*******************************************************************/

#ifndef CPROVER_GOTO_CC_GOTO_CC_MODE_H
#define CPROVER_GOTO_CC_GOTO_CC_MODE_H

#include <langapi/language_ui.h>

#include "goto_cc_cmdline.h"

class goto_cc_modet:public language_uit
{
public:
  virtual int main(int argc, const char **argv);
  virtual int doit()=0;
  virtual void help_mode()=0;
  virtual void help();
  virtual void usage_error();

  goto_cc_modet(
    goto_cc_cmdlinet &_cmdline,
    const std::string &_base_name);
  ~goto_cc_modet();

protected:
  ui_message_handlert ui_message_handler;
  const std::string base_name;
  void register_languages();
  goto_cc_cmdlinet &cmdline;
};

#endif // CPROVER_GOTO_CC_GOTO_CC_MODE_H
