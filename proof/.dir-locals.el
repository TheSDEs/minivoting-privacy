((easycrypt-mode .
  ((eval .
    (flet ((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
           (setq easycrypt-load-path
                 `(,(pre ".")
                   ,(pre "core")
                   ,(pre "Voting")
                   ,(pre "MiniVoting")
                   ,(pre "Helios")
                   ,(pre "Helios/Helios_hom")
                   ,(pre "Helios/Helios_mix"))))
    ))))
