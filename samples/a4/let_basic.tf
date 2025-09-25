seq{
  let account = fetch_account(id="acct-42");
  process(target=account);
  include "lib/common.tf";
}
