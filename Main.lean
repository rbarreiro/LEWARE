import LEWARE

def schema :=
  SchemaDef.new "caaty"
  [
    (
      "chatMessage",
      .tuple [.string, .string],
      .record [
        ("timestamp", .datetime),
        (
          "content",
          .sum [
            (
              "userMessage",
              .record [("text", .string)]
            ),
            (
              "form",
              .record [
              ]
            )
          ]
        )
      ]
    )
  ]


def server := #server [schema]{
  .dbService
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := .option .string,
      roles := .roles ["user", "admin"]
    }
    (
      llet "_" ::: InsertResTy :=
        insertIdValue
          var("chatMessage")
          (t2 var("chatId") uuid)
          r{"timestamp" = now, "content" = cons("userMessage", r{"text" = var("message") } ) };
      none
    )
}

def app := #app [server]{

}

def main : IO Unit :=
  IO.println $ escape_string "Hello!\nyou"

#eval main
