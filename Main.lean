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
      res := option .string,
      roles := .roles ["user", "admin"]
    }
    (
      llet x ::: InsertResTy :=
        insertIdValue @@
          &chatMessage @@
          (t2 @@ &chatId @@ uuid) @@
          r{"timestamp" = now, "content" = cons(userMessage, r{"text" = &message } ) };
      none
    )
}


def app := #app [server] {
    (.root, text @@ "ola")
}

#eval genApp app

def main : IO Unit :=
  IO.println $ "Hello!\nyou"
